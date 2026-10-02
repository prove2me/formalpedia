-- Prove2me | solution 1 for SupportVectorMachines.Calibration.lemma_3_4_bayes_risk_via_inner_risk
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:12:53.731848+00:00
-- url     : https://prove2.me/submissions/5e4ea67f-5f8f-49f8-91c2-47e145425270

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace

set_option autoImplicit false

namespace CexC907

open MeasureTheory SupportVectorMachines.Calibration

/-- `Bool` with the trivial σ-algebra `⊥` is "complete" in the sense of the bundle:
its only null measurable set (for `dirac true`) is `∅`. -/
theorem complete_bot : @IsCompleteMeasurableSpace Bool ⊥ := by
  refine ⟨@Measure.dirac Bool ⊥ true, @Measure.dirac.isProbabilityMeasure Bool ⊥ true, ?_⟩
  rintro s ⟨t, ht, ht0, hst⟩
  rcases (@MeasurableSpace.measurableSet_bot_iff Bool t).1 ht with h | h
  · subst h
    have : s = ∅ := Set.subset_empty_iff.1 hst
    subst this
    exact @MeasurableSet.empty Bool ⊥
  · subst h
    exfalso
    have h1 := @measure_univ Bool ⊥ (@Measure.dirac Bool ⊥ true)
      (@Measure.dirac.isProbabilityMeasure Bool ⊥ true)
    rw [ht0] at h1
    exact zero_ne_one h1

/-- The (non-measurable in `x`) loss. -/
def Lc : Loss Bool := fun x _ _ => if x then 0 else 1

theorem mir_true : minInnerRisk Lc (Measure.dirac (0 : ℝ)) true = 0 := by
  simp [minInnerRisk, innerRisk, Lc]

theorem mir_false : minInnerRisk Lc (Measure.dirac (0 : ℝ)) false = 1 := by
  simp [minInnerRisk, innerRisk, Lc]

theorem not_meas :
    ¬ @Measurable Bool ENNReal ⊥ _ (fun x => minInnerRisk Lc (Measure.dirac (0 : ℝ)) x) := by
  intro hm
  have hs : @MeasurableSet Bool ⊥ ((fun x => minInnerRisk Lc (Measure.dirac (0 : ℝ)) x) ⁻¹' {0}) :=
    hm (measurableSet_singleton 0)
  have hpre : ((fun x => minInnerRisk Lc (Measure.dirac (0 : ℝ)) x) ⁻¹' {0}) = {true} := by
    ext b
    cases b <;> simp [mir_true, mir_false]
  rw [hpre] at hs
  rcases (@MeasurableSpace.measurableSet_bot_iff Bool {true}).1 hs with h | h
  · have : true ∈ ({true} : Set Bool) := rfl
    rw [h] at this
    exact this
  · have : false ∈ ({true} : Set Bool) := by rw [h]; trivial
    simp at this

end CexC907

open MeasureTheory SupportVectorMachines.Calibration in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x)),
    Measurable (fun x => minInnerRisk L (κ x) x) ∧
      bayesRisk L PX κ = ∫⁻ x, minInnerRisk L (κ x) x ∂PX) := by
  intro h
  exact CexC907.not_meas
    (@h Bool ⊥ CexC907.complete_bot CexC907.Lc (@Measure.dirac Bool ⊥ true)
      (@Measure.dirac.isProbabilityMeasure Bool ⊥ true) (fun _ => Measure.dirac (0 : ℝ))
      (@measurable_const (Measure ℝ) Bool _ ⊥ (Measure.dirac (0 : ℝ)))
      (fun _ => inferInstance)).1
