-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.proper_span_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:11:00.449211+00:00
-- url     : https://prove2.me/submissions/5ec8298b-bdfb-4be2-ab54-fa7fa1fe4941

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
namespace ThreeSum.TernaryOriginalRowMenu
theorem _root_.solution (Λ : ℕ) (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) :
    ∃ v : Fin Λ → K, v ≠ 0 ∧ ∀ w ∈ V, ∑ i, v i * w i = 0 := by
  have ha : V.dualAnnihilator ≠ ⊥ := by
    intro h
    exact hV (Submodule.dualAnnihilator_eq_bot_iff.mp h)
  obtain ⟨φ,hφ,hne⟩ := V.dualAnnihilator.ne_bot_iff.mp ha
  let v := (dotProductEquiv K (Fin Λ)).symm φ
  have he : dotProductEquiv K (Fin Λ) v = φ := LinearEquiv.apply_symm_apply _ _
  refine ⟨v, ?_, ?_⟩
  · intro hz
    apply hne
    rw [← he,hz,map_zero]
  · intro w hw
    have hh := (Submodule.mem_dualAnnihilator φ).mp hφ w hw
    rw [← he] at hh
    exact hh
end ThreeSum.TernaryOriginalRowMenu
