-- Prove2me | solution 1 for ReciprocityTheory.PGsh.constantCoeff_rowSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:40:46.777258+00:00
-- url     : https://prove2.me/submissions/b94a72f5-3164-4129-a46e-3e629893b992

import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Theorems.Thm_ReciprocityTheory_PGsh_rowSubst_X
import Theorems.Thm_ReciprocityTheory_PGsh_rowSubst_C

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
theorem _root_.solution (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    constantCoeff (rowSubst h Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [rowSubst_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => simp [map_mul, hp, rowSubst_X]
end ReciprocityTheory.PGsh
