-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:31.224499+00:00
-- url     : https://prove2.me/submissions/2e14af3d-87cc-42af-a162-984c5e8b9ab1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_sum_sA_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
theorem _root_.solution {M : Type*} [AddCommMonoid M] {k : ℕ} (w : Fin (k + 1))
    (H : Fin (k + 1) → Fin (k + 1) → Fin (k + 1) → M) :
    ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)
      = ∑ j : Fin k, ∑ x' : Fin (k + 1), ∑ y : Fin k, H (w.succAbove j) (x'.succAbove y) x' := by
  have h1 : ∀ w' : Fin (k + 1), (∑ x : Fin (k + 1), ∑ x' : Fin (k + 1),
      (if w ≠ w' ∧ x ≠ x' then H w' x x' else 0)) =
      if w ≠ w' then ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1), (if x ≠ x' then H w' x x' else 0) else 0 := by
    intro w'
    by_cases hw : w ≠ w'
    · simp [hw]
    · simp [hw]
  rw [Finset.sum_congr rfl fun w' _ => h1 w', sum_sA_ite]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  have h2 : ∀ x : Fin (k + 1), (if x ≠ x' then H (w.succAbove j) x x' else 0) =
      if x' ≠ x then H (w.succAbove j) x x' else 0 := by
    intro x
    by_cases h : x = x'
    · subst h
      rfl
    · rw [if_pos h, if_pos (Ne.symm h)]
  rw [Finset.sum_congr rfl fun x _ => h2 x]
  exact sum_sA_ite x' (fun x => H (w.succAbove j) x x')
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
