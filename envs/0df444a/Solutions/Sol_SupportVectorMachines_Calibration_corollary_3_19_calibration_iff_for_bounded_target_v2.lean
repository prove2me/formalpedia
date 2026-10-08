-- Prove2me | solution 1 for SupportVectorMachines.Calibration.corollary_3_19_calibration_iff_for_bounded_target_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T16:20:24.212286+00:00
-- url     : https://prove2.me/submissions/f923943b-840d-4ba2-9918-d73db9935baa

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction_v2
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2

set_option autoImplicit false

namespace CexCC1901BE

open MeasureTheory SupportVectorMachines.Calibration

/-- Target loss: `min |t| 1` (bounded by `1`). -/
noncomputable def Ltar : Loss Unit where
  toFun := fun _ _ t => min |t| 1
  measurable := by
    have : Continuous (fun p : Unit × ℝ × ℝ => min |p.2.2| 1) := by fun_prop
    exact this.measurable
  nonneg := fun _ _ t => le_min (abs_nonneg t) zero_le_one

/-- Surrogate loss: identically `0`. -/
noncomputable def Lsur : Loss Unit where
  toFun := fun _ _ _ => 0
  measurable := measurable_const
  nonneg := fun _ _ _ => le_refl 0

/-- A non-probability measure: `2 • δ₀`. -/
noncomputable def Q : Measure ℝ := (2 : ENNReal) • Measure.dirac 0

theorem innerRisk_Ltar (t : ℝ) :
    innerRisk Ltar Q () t = 2 * ENNReal.ofReal (min |t| 1) := by
  simp [innerRisk, Q, Ltar, mul_comm]

theorem innerRisk_Lsur (t : ℝ) : innerRisk Lsur Q () t = 0 := by
  simp [innerRisk, Lsur]

theorem not_calibrated : ¬ IsCalibrated Ltar Lsur {Q} := by
  intro h
  have hpos := h 1 one_pos Q rfl ()
  have hminS : minInnerRisk Lsur Q () ≠ ⊤ := by
    have : minInnerRisk Lsur Q () ≤ innerRisk Lsur Q () 0 := iInf_le _ 0
    rw [innerRisk_Lsur] at this
    exact ne_top_of_le_ne_top ENNReal.zero_ne_top this
  have hminT : minInnerRisk Ltar Q () = 0 := by
    have : minInnerRisk Ltar Q () ≤ innerRisk Ltar Q () 0 := iInf_le _ 0
    rw [innerRisk_Ltar] at this
    simpa using this
  have h1 : (1 : ℝ) ∉ approxMinimizers Ltar Q () 1 := by
    simp only [approxMinimizers, Set.mem_ofPred_eq, innerRisk_Ltar, hminT, zero_add]
    norm_num
  have hzero : calibrationFunction Ltar Lsur Q () 1 = 0 := by
    unfold calibrationFunction
    rw [if_neg hminS]
    apply le_antisymm _ (zero_le)
    calc (⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Ltar Q () 1}, innerRisk Lsur Q () t) -
          minInnerRisk Lsur Q ()
        ≤ ⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Ltar Q () 1}, innerRisk Lsur Q () t := tsub_le_self
      _ ≤ innerRisk Lsur Q () 1 := iInf₂_le (1 : ℝ) h1
      _ = 0 := innerRisk_Lsur 1
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

theorem complete_unit : IsCompleteMeasurableSpace Unit := fun s _ => MeasurableSet.of_discrete

theorem prob_not_Q (μ : Measure ℝ) [IsProbabilityMeasure μ] : μ ∉ ({Q} : Set (Measure ℝ)) := by
  intro hμ
  have h1 : μ Set.univ = Q Set.univ := by rw [Set.mem_singleton_iff.mp hμ]
  simp [Q] at h1

end CexCC1901BE

open MeasureTheory SupportVectorMachines.Calibration in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ))
    (B : ℝ) (hBdd : ∀ x y t, Ltar x y t ≤ B),
    IsCalibrated Ltar Lsur 𝒬 ↔
      ∀ ε : ENNReal, 0 < ε →
        ∀ (PX : Measure X) (κ : X → Measure ℝ), Measurable κ → IsProbabilityMeasure PX →
          (∀ x, IsProbabilityMeasure (κ x)) →
          IsOfType κ PX 𝒬 → bayesRisk Lsur PX κ < ⊤ →
          ∃ δ : ENNReal, 0 < δ ∧
            ∀ f : X → ℝ, Measurable f →
              outerRisk Lsur PX κ f < bayesRisk Lsur PX κ + δ →
              outerRisk Ltar PX κ f < bayesRisk Ltar PX κ + ε) := by
  intro h
  apply CexCC1901BE.not_calibrated
  refine (h (X := Unit) CexCC1901BE.complete_unit CexCC1901BE.Ltar CexCC1901BE.Lsur
    {CexCC1901BE.Q} 1 (fun _ _ t => min_le_right |t| 1)).mpr ?_
  intro ε _ PX κ _ hPX hκ hType _
  exfalso
  obtain ⟨x, hx⟩ := hType.exists
  exact CexCC1901BE.prob_not_Q (κ x) hx
