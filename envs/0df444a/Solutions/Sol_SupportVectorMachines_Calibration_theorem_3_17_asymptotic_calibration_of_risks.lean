-- Prove2me | solution 1 for SupportVectorMachines.Calibration.theorem_3_17_asymptotic_calibration_of_risks
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:03:50.728811+00:00
-- url     : https://prove2.me/submissions/53388f3e-67ac-4da9-991a-51d1cdf81691

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_CalibrationFunction
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

set_option autoImplicit false

open MeasureTheory

namespace SupportVectorMachines.Calibration
namespace Cex1c5daa33

/-- A two-point space carrying the trivial σ-algebra. -/
inductive Pt : Type
  | a
  | b
  deriving DecidableEq

instance : MeasurableSpace Pt := ⊥

def Ltar : Loss Pt := fun _ _ t => |t|

def Lsur : Loss Pt := fun x _ t => if x = Pt.a then |t| else 0

theorem inner_const (L : Loss Pt) (x : Pt) (t : ℝ) (c : ℝ) (hc : ∀ y, L x y t = c) :
    innerRisk L (Measure.dirac (0:ℝ)) x t = ENNReal.ofReal c := by
  unfold innerRisk
  simp [hc]

theorem minInner_zero (L : Loss Pt) (x : Pt) (hL : ∀ y, L x y 0 = 0) :
    minInnerRisk L (Measure.dirac (0:ℝ)) x = 0 := by
  unfold minInnerRisk
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le 0 ?_
  rw [inner_const L x 0 0 hL]
  simp

theorem hX : IsCompleteMeasurableSpace Pt := by
  refine ⟨Measure.dirac Pt.a, inferInstance, ?_⟩
  rintro s ⟨t, ht, h0, hst⟩
  rcases MeasurableSpace.measurableSet_bot_iff.mp ht with rfl | rfl
  · rw [Set.subset_empty_iff.mp hst]
    exact MeasurableSet.empty
  · rw [measure_univ] at h0
    exact absurd h0 one_ne_zero

theorem cal_b : calibrationFunction Ltar Lsur (Measure.dirac (0:ℝ)) Pt.b 1 = 0 := by
  have hm : minInnerRisk Lsur (Measure.dirac (0:ℝ)) Pt.b = 0 :=
    minInner_zero Lsur Pt.b (fun y => by simp [Lsur])
  unfold calibrationFunction
  rw [hm, if_neg ENNReal.zero_ne_top, tsub_zero]
  refine le_antisymm ?_ bot_le
  have hmem : (1:ℝ) ∈ {t : ℝ | t ∉ approxMinimizers Ltar (Measure.dirac (0:ℝ)) Pt.b 1} := by
    simp only [Set.mem_setOf_eq, approxMinimizers]
    rw [inner_const Ltar Pt.b 1 1 (fun y => by simp [Ltar]),
      minInner_zero Ltar Pt.b (fun y => by simp [Ltar])]
    simp
  refine iInf₂_le_of_le 1 hmem ?_
  rw [inner_const Lsur Pt.b 1 0 (fun y => by simp [Lsur])]
  simp

theorem cal_a : 1 ≤ calibrationFunction Ltar Lsur (Measure.dirac (0:ℝ)) Pt.a 1 := by
  have hm : minInnerRisk Lsur (Measure.dirac (0:ℝ)) Pt.a = 0 :=
    minInner_zero Lsur Pt.a (fun y => by simp [Lsur])
  unfold calibrationFunction
  rw [hm, if_neg ENNReal.zero_ne_top, tsub_zero]
  refine le_iInf₂ fun t ht => ?_
  simp only [Set.mem_setOf_eq, approxMinimizers] at ht
  rw [inner_const Ltar Pt.a t |t| (fun y => by simp [Ltar]),
    minInner_zero Ltar Pt.a (fun y => by simp [Ltar]), zero_add] at ht
  rw [inner_const Lsur Pt.a t |t| (fun y => by simp [Lsur])]
  exact not_lt.mp ht

theorem bayes_fin (L : Loss Pt) (hL : ∀ x y, L x y 0 = 0) :
    bayesRisk L (Measure.dirac Pt.a) (fun _ => Measure.dirac (0:ℝ)) < ⊤ := by
  have h : bayesRisk L (Measure.dirac Pt.a) (fun _ => Measure.dirac (0:ℝ)) = 0 := by
    refine le_antisymm ?_ bot_le
    unfold bayesRisk
    refine iInf₂_le_of_le (fun _ => (0:ℝ)) measurable_const ?_
    unfold outerRisk
    simp only [inner_const L _ 0 0 (hL _)]
    simp
  rw [h]
  exact ENNReal.zero_lt_top

theorem not_meas :
    ¬ Measurable (fun x : Pt => calibrationFunction Ltar Lsur (Measure.dirac (0:ℝ)) x 1) := by
  intro hm
  have hs := hm (measurableSet_singleton (0 : ENNReal))
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with h | h
  · have : Pt.b ∈ (fun x : Pt => calibrationFunction Ltar Lsur (Measure.dirac (0:ℝ)) x 1) ⁻¹'
        {0} := by
      simp [cal_b]
    rw [h] at this
    exact this
  · have : Pt.a ∈ (fun x : Pt => calibrationFunction Ltar Lsur (Measure.dirac (0:ℝ)) x 1) ⁻¹'
        {0} := by
      rw [h]; trivial
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
    have h1 := cal_a
    rw [this] at h1
    exact absurd h1 (by simp)

end Cex1c5daa33

end SupportVectorMachines.Calibration

open SupportVectorMachines.Calibration in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (Ltar Lsur : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x))
    (hLtar : bayesRisk Ltar PX κ < ⊤) (hLsur : bayesRisk Lsur PX κ < ⊤),
    (∀ ε : ENNReal, Measurable (fun x => calibrationFunction Ltar Lsur (κ x) x ε)) ∧
    ((∀ ε : ENNReal, 0 < ε →
        ∃ δ : ENNReal, 0 < δ ∧ ∀ f : X → ℝ, Measurable f →
          outerRisk Lsur PX κ f < bayesRisk Lsur PX κ + δ →
          outerRisk Ltar PX κ f < bayesRisk Ltar PX κ + ε) →
      ∀ ε : ENNReal, 0 < ε →
        PX {x : X | calibrationFunction Ltar Lsur (κ x) x ε = 0} = 0) ∧
    ((∃ b : X → ℝ, (∀ x, 0 ≤ b x) ∧ Integrable b PX ∧
        ∀ x t, innerRisk Ltar (κ x) x t ≤ minInnerRisk Ltar (κ x) x + ENNReal.ofReal (b x)) →
      (∀ ε : ENNReal, 0 < ε →
          PX {x : X | calibrationFunction Ltar Lsur (κ x) x ε = 0} = 0) →
      ∀ ε : ENNReal, 0 < ε →
        ∃ δ : ENNReal, 0 < δ ∧ ∀ f : X → ℝ, Measurable f →
          outerRisk Lsur PX κ f < bayesRisk Lsur PX κ + δ →
          outerRisk Ltar PX κ f < bayesRisk Ltar PX κ + ε)) := by
  intro H
  have key := @H SupportVectorMachines.Calibration.Cex1c5daa33.Pt _ SupportVectorMachines.Calibration.Cex1c5daa33.hX SupportVectorMachines.Calibration.Cex1c5daa33.Ltar SupportVectorMachines.Calibration.Cex1c5daa33.Lsur
    (Measure.dirac SupportVectorMachines.Calibration.Cex1c5daa33.Pt.a) _ (fun _ => Measure.dirac (0:ℝ)) measurable_const
    (fun _ => inferInstance)
    (SupportVectorMachines.Calibration.Cex1c5daa33.bayes_fin _ (fun x y => by simp [SupportVectorMachines.Calibration.Cex1c5daa33.Ltar]))
    (SupportVectorMachines.Calibration.Cex1c5daa33.bayes_fin _ (fun x y => by simp [SupportVectorMachines.Calibration.Cex1c5daa33.Lsur]))
  exact SupportVectorMachines.Calibration.Cex1c5daa33.not_meas (key.1 1)
