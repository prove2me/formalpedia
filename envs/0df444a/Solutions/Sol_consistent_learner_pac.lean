-- Prove2me | solution 1 for consistent_learner_pac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:43.201436+00:00
-- url     : https://prove2.me/submissions/d488a0f7-af3d-4021-96c6-28f62343237f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas
public import Theorems.Thm_P2M_vcdim_finite_imp_uc__685a2436ce92
public import Theorems.Thm_uc_imp_pac

section
@[expose] public section
universe u
attribute [local instance] Classical.propDecidable
section UCNotOnline
end UCNotOnline
private theorem pacLearnable_of_vcdim_finite (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) : PACLearnable X C := by
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hvcdim hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C)
    (L : BatchLearner X Bool)
    (_hcons : ∀ {m : ℕ} (S : Fin m → X × Bool), ∀ i, L.learn S (S i).1 = (S i).2) :
    PACLearnable X C :=
  pacLearnable_of_vcdim_finite X C hvcdim hmeas_C hc_meas hWB
