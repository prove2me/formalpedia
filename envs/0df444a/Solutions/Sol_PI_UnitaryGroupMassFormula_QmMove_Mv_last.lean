-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.Mv_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:08.488469+00:00
-- url     : https://prove2.me/submissions/531d64fc-6d97-46d7-8732-278ac488d41a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sum_perms_sign_squared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Pv_last
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_phiL_castSucc
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_phiL_last
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_phiL_sign
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sum_phiL


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmMove
variable {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
  (a : Fin m → Fin n) (b : Fin (m + 1) → Fin n) (w : ℂ)
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution (hE : GlRel E) : Mv E y a b w m = (m.factorial : A) * ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) * (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by
  unfold Mv
  rw [sum_phiL m, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hP : ∀ ρ, Pv E y a b w m (lastColumnSplit m (j, ρ)) =
      (((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a (b ∘ j.succAbove) (w - 1)) * y (b j) := by
    intro ρ
    rw [Pv_last, phiL_last, ← quantumMinorColSkew_holds A n m E hE a (b ∘ j.succAbove) ρ (w - 1)]
    congr 2
    funext k
    simp [phiL_castSucc]
  simp only [hP, phiL_sign, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact sum_perms_sign_squared m _ _ _
end PI.UnitaryGroupMassFormula.QmMove
