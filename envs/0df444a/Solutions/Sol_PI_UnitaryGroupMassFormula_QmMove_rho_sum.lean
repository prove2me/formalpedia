-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.rho_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:21.45646+00:00
-- url     : https://prove2.me/submissions/0bd86fe3-f2e3-4121-b6ed-92352893ab58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmMove_sgnlem


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
namespace PI.UnitaryGroupMassFormula.QmMove
theorem _root_.solution {A : Type*} [Ring A] (m : ℕ) (z : ℤ) (x D : A) :
    ∑ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (m.factorial : A) * ((z : A) * (x * D)) := by
  have h : ∀ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      (x * (((Equiv.Perm.sign ρ : ℤ) : A) * D)) = (z : A) * (x * D) := by
    intro ρ
    rw [sgnlem, ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A), ← Int.cast_mul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
end PI.UnitaryGroupMassFormula.QmMove
