-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayley_int_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:25.137149+00:00
-- url     : https://prove2.me/submissions/6a11b765-c3e4-4e27-86e3-6f7b41ccd0bf

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_detPoly_mul_cayleyOmega_pow

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
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (s : ℕ) :
    cayOp n ℤ (cayDet n ℤ ^ (s + 1)) =
      C (eval onePt (cayOp n ℤ (cayDet n ℤ ^ (s + 1)))) * cayDet n ℤ ^ s := by
  have h := detPoly_mul_cayleyOmega_pow (n := n) (s + 1)
  have hne : cayDet n ℤ ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) ℤ
  apply mul_left_cancel₀ hne
  rw [h]; ring
end ReciprocityTheory.PGsh
