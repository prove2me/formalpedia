-- Prove2me | solution 1 for P2M_vcdim_finite_imp_pac_via_uc__c09ebcf0a1b4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:36.918596+00:00
-- url     : https://prove2.me/submissions/ff55a225-1c2d-430b-9ca0-ddab1bf1a35e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Theorems.Thm_P2M_vcdim_finite_imp_uc__685a2436ce92
public import Theorems.Thm_uc_imp_pac


set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C := by
  by_cases hne : C.Nonempty
  · exact uc_imp_pac X C hne (vcdim_finite_imp_uc' X C hC hmeas_C hc_meas hWB)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
