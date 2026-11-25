-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.colPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:26.586994+00:00
-- url     : https://prove2.me/submissions/e300deb8-8beb-43fb-a75b-72eac812e943

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_qminor_bS_eq
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
theorem _root_.solution (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (hG : GlRel E) (e : Fin n) (f : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (he : ∀ x, b x ≠ e) (u : ℂ) :
    qminor E (bS f e) b u = ∑ x : Fin (t + 1), (((-1 : ℤ) ^ (t + (x : ℕ)) : ℤ) : A) *
      (E e (b x) * qminor E f (b ∘ x.succAbove) u) := by
  rw [qminor_bS_eq, hF A n t E hG (bE e f) b u, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : bE e f ∘ Fin.succ = f := by
    funext i
    simp [bE]
  have h2 : bE e f 0 = e := by simp [bE]
  rw [h1, h2, Tm_of_ne E _ (Ne.symm (he x)), ← mul_assoc, ← Int.cast_mul, ← pow_add]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
