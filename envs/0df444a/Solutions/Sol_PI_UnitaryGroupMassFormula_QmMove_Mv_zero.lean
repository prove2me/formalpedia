-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.Mv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:48.25797+00:00
-- url     : https://prove2.me/submissions/9274cda7-940f-4c67-87b4-922540cab40a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_rho_sum
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_Pv_zero
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_firstColumnSplit_succ
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_firstColumnSplit_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sign_firstColumnSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sum_perm_eq_sum_firstColumnSplit


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
theorem _root_.solution (hE : GlRel E) : Mv E y a b w 0 = (m.factorial : A) * ∑ j : Fin (m + 1),
    (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) := by
  unfold Mv
  rw [sum_perm_eq_sum_firstColumnSplit m, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hP : ∀ ρ, Pv E y a b w 0 (phi0 m (j, ρ)) =
      y (b j) * (((Equiv.Perm.sign ρ : ℤ) : A) * qminor E a (b ∘ j.succAbove) w) := by
    intro ρ
    rw [Pv_zero, firstColumnSplit_zero, ← quantumMinorColSkew_holds A n m E hE a (b ∘ j.succAbove) ρ w]
    congr 2
    funext k
    simp [firstColumnSplit_succ]
  simp only [hP, sign_firstColumnSplit, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  exact rho_sum m _ _ _
end PI.UnitaryGroupMassFormula.QmMove
