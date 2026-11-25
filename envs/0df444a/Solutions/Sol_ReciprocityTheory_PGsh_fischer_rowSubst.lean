-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_rowSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:11.456237+00:00
-- url     : https://prove2.me/submissions/6ef0e255-68e1-4622-ba30-bb51593f9c2c

import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Theorems.Thm_ReciprocityTheory_PGsh_rowSubst_X
import Theorems.Thm_ReciprocityTheory_PGsh_rowSubst_C
import Theorems.Thm_ReciprocityTheory_PGsh_coeff_zero_rowSubst
import Theorems.Thm_ReciprocityTheory_PGsh_pderiv_rowSubst
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_C_left
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_add_left
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_mul_X
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_smul_left
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_smul_right
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_sum_left
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    rw [rowSubst_C, fischer_C_left, fischer_C_left, coeff_zero_rowSubst]
  | add p q hp hq =>
    rw [map_add, fischer_add_left, fischer_add_left, hp, hq]
  | mul_X p n hp =>
    rcases n with ⟨k, a⟩
    rw [map_mul, rowSubst_X, Finset.mul_sum, fischer_sum_left, fischer_mul_X, pderiv_rowSubst,
      fischer_sum_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_left_comm, MvPolynomial.C_mul', fischer_smul_left, fischer_mul_X, hp, MvPolynomial.C_mul',
      fischer_smul_right]
    simp [Matrix.conjTranspose_apply]
end ReciprocityTheory.PGsh
