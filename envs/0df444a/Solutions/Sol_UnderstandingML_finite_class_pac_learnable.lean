-- Prove2me | solution 1 for UnderstandingML.finite_class_pac_learnable
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T12:41:23.803396+00:00
-- url     : https://prove2.me/submissions/594dab74-298f-4a92-b26e-0471213401bc

import Definitions.Def_UnderstandingML_Framework
import Theorems.Thm_UnderstandingML_erm_finite_class_bound

open MeasureTheory UnderstandingML

theorem solution {X : Type*} [MeasurableSpace X] (H : Finset (X → Bool))
    (hne : H.Nonempty) (hH : ∀ h ∈ H, Measurable h) :
    (∃ A : Learner (X × Bool) (X → Bool), IsERMLearner loss01 (↑H) A ∧
      IsPACWith (↑H) A (fun ε δ ↦ ⌈Real.log (H.card / δ) / ε⌉₊)) ∧
    PACLearnable (↑H : Set (X → Bool)) := by
  classical
  let A : Learner (X × Bool) (X → Bool) := fun m S ↦
    (H.exists_min_image (empRisk loss01 S) hne).choose
  have hA : IsERMLearner loss01 (↑H) A := fun m S ↦
    (H.exists_min_image (empRisk loss01 S) hne).choose_spec
  have hPAC : IsPACWith (↑H) A (fun ε δ ↦ ⌈Real.log (H.card / δ) / ε⌉₊) := by
    intro ε δ hε _ hδ hδ1 D _ f hf hreal m hm
    refine le_trans (measure_mono ?_)
      (erm_finite_class_bound H hH hε hδ hδ1 m (Nat.ceil_le.mp hm) D f hf hreal)
    intro S hS
    exact ⟨A m S, hA m S, hS⟩
  exact ⟨⟨A, hA, hPAC⟩, _, A, hPAC⟩
