-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.double_row_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:36.286442+00:00
-- url     : https://prove2.me/submissions/1d1b633e-f570-4b8d-b9e8-71b4284fe475

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_DoubleRowDecreasing
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_sign_sq_cast
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution : DblDec := by
  unfold DblDec
  intro A _ _ n t E hE a b u
  have hcol := Formalism.REAL.quantumMinorColSkew_holds A n t E hE a b
  unfold doubleRowFormSum
  rw [Finset.sum_comm]
  rw [show (t.factorial : ℂ) • qminor E a b u = ∑ _τ : Equiv.Perm (Fin t), qminor E a b u by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul]]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := hcol τ u
  unfold qminor at h
  simp only [Function.comp_apply] at h
  have e : ∀ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : A) =
      ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign σ : ℤ) : A) := by
    intro σ
    rw [Int.cast_mul, (Int.cast_commute _ _).eq]
  simp_rw [e, mul_assoc, ← Finset.mul_sum]
  rw [h, ← mul_assoc, sign_sq_cast, one_mul]
  rfl
end PI.UnitaryGroupMassFormula.QmRowForm
