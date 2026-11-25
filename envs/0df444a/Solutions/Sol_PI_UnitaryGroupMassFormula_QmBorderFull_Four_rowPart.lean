-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.rowPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:05.334282+00:00
-- url     : https://prove2.me/submissions/9c2976a4-400d-4e9c-b0ea-89802e797608

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_neg_one_pow_mul_self
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_qminor_bE_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_Tm_of_ne

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
theorem _root_.solution (hR : ExpLastRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (bE e f) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) *
      (qminor E f (b ∘ x.succAbove) (u - 1) * E e (b x)) := by
  rw [qminor_bE_eq, hR A n t E hG (bS f e) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : bS f e ∘ Fin.castSucc = f := by
    funext i
    simp [bS]
  have h2 : bS f e (Fin.last t) = e := by simp [bS]
  have hs : (-1 : ℤ) ^ t * (-1 : ℤ) ^ (t + (x : ℕ)) = (-1 : ℤ) ^ (x : ℕ) := by
    rw [pow_add, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [h1, h2, Tm_of_ne E u (Ne.symm (he x)), ← mul_assoc, ← Int.cast_mul, hs]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
