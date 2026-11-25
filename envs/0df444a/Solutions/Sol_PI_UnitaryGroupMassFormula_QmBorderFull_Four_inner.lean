-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:58:46.150372+00:00
-- url     : https://prove2.me/submissions/5d9ce914-6e49-4996-b1a1-41decbdf680d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_rowPart
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_colPart

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
theorem _root_.solution (hR : ExpLastRow) (hF : ExpFirstRow) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hG : GlRel E) (e es : Fin n) (W : Fin t → Fin n) (b : Fin (t + 2) → Fin n)
    (he : ∀ x, b x ≠ e) (hes : ∀ x, b x ≠ es) (z : ℂ) :
    qminor E (bE e (bS W es)) b z = ∑ x : Fin (t + 2), ∑ y : Fin (t + 1),
      (((-1 : ℤ) ^ ((x : ℕ) + t + (y : ℕ)) : ℤ) : A) *
        (E es (b (x.succAbove y)) * qminor E W ((b ∘ x.succAbove) ∘ y.succAbove) (z - 1) * E e (b x)) := by
  rw [rowPart hR E hG e (bS W es) b he z]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [colPart hF E hG es W (b ∘ x.succAbove) (fun y => hes _) (z - 1), Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Function.comp_apply, ← mul_assoc, ← Int.cast_mul, ← pow_add, add_assoc]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
