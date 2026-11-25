-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.transvection_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:28.708224+00:00
-- url     : https://prove2.me/submissions/b5d6bfa3-e368-42b3-9c7e-8fe7378ecff8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_UniHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open MeasureTheory
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution {A : Type} [CommRing A] {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : A) :
    IsLowUni (Matrix.transvection i j c) ∨ IsLowUni (Matrix.transvection i j c).transpose := by
  have key : ∀ a b : Fin k, (i = a ∧ j = b → False) → Matrix.single i j c a b = 0 := fun a b h => by
    rw [Matrix.single_apply, if_neg (fun hh => h hh)]
  have tac : ∀ a b : Fin k, (a < b ∧ i = a ∧ j = b → False) ∨ True := fun _ _ => Or.inr trivial
  rcases lt_or_gt_of_ne hij with h | h
  · right
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_gt hab), key b a (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]
  · left
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_lt hab), key a b (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]
end PI.VolSemiDirect.W.Cj
