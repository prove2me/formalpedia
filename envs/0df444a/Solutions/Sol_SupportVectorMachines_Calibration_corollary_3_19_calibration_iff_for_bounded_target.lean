-- Prove2me | solution 1 for SupportVectorMachines.Calibration.corollary_3_19_calibration_iff_for_bounded_target
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:32:15.609576+00:00
-- url     : https://prove2.me/submissions/f7f32a71-a962-4942-894c-4713cbb4c172

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

set_option autoImplicit false

namespace Cex89589f2d

open MeasureTheory SupportVectorMachines.Calibration

/-- Two points carrying the trivial σ-algebra `{∅, univ}`. -/
def CX : Type := Bool

instance instMSCX : MeasurableSpace CX := ⊥

/-- The point `false`, where calibration fails. -/
def xBad : CX := (false : Bool)

/-- The point `true`, where the target loss vanishes identically. -/
def xGood : CX := (true : Bool)

/-- Bounded target loss: zero at `xGood`; at `xBad` it is `0` for `t = 0` and `1` otherwise. -/
noncomputable def Lt : Loss CX := fun x _ t =>
  bif (show Bool from x) then 0 else if t = 0 then 0 else 1

/-- Surrogate loss: identically zero. -/
noncomputable def Ls : Loss CX := fun _ _ _ => 0

theorem hBdd : ∀ x y t, Lt x y t ≤ 1 := by
  intro x y t
  unfold Lt
  cases (show Bool from x) <;> split_ifs <;> norm_num

theorem hXc : IsCompleteMeasurableSpace CX := by
  refine ⟨Measure.dirac xGood, inferInstance, ?_⟩
  rintro s ⟨t, ht, h0, hst⟩
  rcases (MeasurableSpace.measurableSet_bot_iff.mp ht) with rfl | rfl
  · rw [Set.subset_empty_iff.mp hst]
    exact MeasurableSet.empty
  · simp at h0

theorem innerRisk_Ls (Q : Measure ℝ) (x : CX) (t : ℝ) : innerRisk Ls Q x t = 0 := by
  simp [innerRisk, Ls]

theorem minInnerRisk_Ls (Q : Measure ℝ) (x : CX) : minInnerRisk Ls Q x = 0 := by
  simp [minInnerRisk, innerRisk_Ls]

theorem innerRisk_Lt_good (Q : Measure ℝ) (t : ℝ) : innerRisk Lt Q xGood t = 0 := by
  simp [innerRisk, Lt, xGood]

theorem innerRisk_Lt_bad (t : ℝ) :
    innerRisk Lt (Measure.dirac (0 : ℝ)) xBad t = ENNReal.ofReal (if t = 0 then 0 else 1) := by
  simp [innerRisk, Lt, xBad]

theorem notCal : ¬ IsCalibrated Lt Ls {Measure.dirac (0 : ℝ)} := by
  intro h
  have h1 := h 1 one_pos (Measure.dirac (0 : ℝ)) rfl xBad
  have hmin : minInnerRisk Lt (Measure.dirac (0 : ℝ)) xBad = 0 := by
    apply le_antisymm _ zero_le
    calc minInnerRisk Lt (Measure.dirac (0 : ℝ)) xBad
        ≤ innerRisk Lt (Measure.dirac (0 : ℝ)) xBad 0 := iInf_le _ 0
      _ = 0 := by rw [innerRisk_Lt_bad]; simp
  have hmem : (1 : ℝ) ∈ {t : ℝ | t ∉ approxMinimizers Lt (Measure.dirac (0 : ℝ)) xBad 1} := by
    simp only [approxMinimizers, hmin, innerRisk_Lt_bad]
    simp
  have hzero : calibrationFunction Lt Ls (Measure.dirac (0 : ℝ)) xBad 1 = 0 := by
    unfold calibrationFunction
    rw [minInnerRisk_Ls, if_neg ENNReal.zero_ne_top]
    have : (⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Lt (Measure.dirac (0 : ℝ)) xBad 1},
        innerRisk Ls (Measure.dirac (0 : ℝ)) xBad t) = 0 := by
      apply le_antisymm _ zero_le
      calc (⨅ t ∈ {t : ℝ | t ∉ approxMinimizers Lt (Measure.dirac (0 : ℝ)) xBad 1},
            innerRisk Ls (Measure.dirac (0 : ℝ)) xBad t)
          ≤ innerRisk Ls (Measure.dirac (0 : ℝ)) xBad 1 := iInf₂_le _ hmem
        _ = 0 := innerRisk_Ls _ _ _
    rw [this]
    simp
  rw [hzero] at h1
  exact lt_irrefl _ h1

/-- Every lower Lebesgue integral over the trivial σ-algebra of a function vanishing at
`xGood` is zero. -/
theorem lintegral_zero_of_good (PX : Measure CX) (F : CX → ENNReal) (hF : F xGood = 0) :
    ∫⁻ x, F x ∂PX = 0 := by
  obtain ⟨g, hg, hgle, heq⟩ := exists_measurable_le_lintegral_eq PX F
  have hS : MeasurableSet (g ⁻¹' {0}) := hg (measurableSet_singleton 0)
  have hgood : xGood ∈ g ⁻¹' {0} := by
    show g xGood = 0
    exact le_antisymm (le_trans (hgle xGood) (le_of_eq hF)) zero_le
  have huniv : g ⁻¹' {0} = Set.univ := by
    rcases (MeasurableSpace.measurableSet_bot_iff.mp hS) with h | h
    · rw [h] at hgood
      exact absurd hgood (Set.notMem_empty _)
    · exact h
  have hg0 : g = 0 := by
    funext x
    have : x ∈ g ⁻¹' {0} := by rw [huniv]; exact Set.mem_univ x
    exact this
  rw [heq, hg0]
  simp

theorem riskImp : ∀ ε : ENNReal, 0 < ε →
    ∀ (PX : Measure CX) (κ : CX → Measure ℝ), Measurable κ → IsProbabilityMeasure PX →
      (∀ x, IsProbabilityMeasure (κ x)) →
      IsOfType κ PX {Measure.dirac (0 : ℝ)} → bayesRisk Ls PX κ < ⊤ →
      ∃ δ : ENNReal, 0 < δ ∧
        ∀ f : CX → ℝ, Measurable f →
          outerRisk Ls PX κ f < bayesRisk Ls PX κ + δ →
          outerRisk Lt PX κ f < bayesRisk Lt PX κ + ε := by
  intro ε hε PX κ _ _ _ _ _
  refine ⟨1, one_pos, fun f _ _ => ?_⟩
  have h0 : outerRisk Lt PX κ f = 0 := by
    unfold outerRisk
    exact lintegral_zero_of_good PX _ (innerRisk_Lt_good _ _)
  rw [h0]
  exact lt_of_lt_of_le hε le_add_self

end Cex89589f2d

open MeasureTheory SupportVectorMachines.Calibration in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (Ltar Lsur : Loss X) (𝒬 : Set (Measure ℝ))
    (B : ℝ) (hB : 0 < B) (hBdd : ∀ x y t, Ltar x y t ≤ B),
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
  exact Cex89589f2d.notCal
    ((h (X := Cex89589f2d.CX) Cex89589f2d.hXc Cex89589f2d.Lt Cex89589f2d.Ls
      {Measure.dirac (0 : ℝ)} 1 one_pos Cex89589f2d.hBdd).mpr Cex89589f2d.riskImp)
