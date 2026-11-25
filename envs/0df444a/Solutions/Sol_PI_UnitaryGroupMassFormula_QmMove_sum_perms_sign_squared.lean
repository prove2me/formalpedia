-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmMove.sum_perms_sign_squared
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:28.558561+00:00
-- url     : https://prove2.me/submissions/c2684470-885c-452d-8712-c3a10b8dddc2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_MoveOperatorCovariance
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared

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
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (m.factorial : A) * ((z : A) * (D * x)) := by
  have h : ∀ ρ : Equiv.Perm (Fin m), (((z * (Equiv.Perm.sign ρ : ℤ)) : ℤ) : A) *
      ((((Equiv.Perm.sign ρ : ℤ) : A) * D) * x) = (z : A) * (D * x) := by
    intro ρ
    rw [Int.cast_mul, mul_assoc, ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A) _ x,
      ← mul_assoc ((Equiv.Perm.sign ρ : ℤ) : A) ((Equiv.Perm.sign ρ : ℤ) : A) D, ← Int.cast_mul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
end PI.UnitaryGroupMassFormula.QmMove
