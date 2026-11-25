-- Prove2me | solution 1 for ReciprocityTheory.PGsh.detPoly_mul_cayleyOmega_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:34:04.129646+00:00
-- url     : https://prove2.me/submissions/b7b4704e-8d28-4f66-817d-b3f8832262b2

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_cayOp_linSub
import Theorems.Thm_ReciprocityTheory_PGsh_linSub_cayDet
import Theorems.Thm_ReciprocityTheory_PGsh_eval_onePt_linSub
import Theorems.Thm_ReciprocityTheory_PGsh_eval_cayDet

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
    cayDet n ℤ * cayOp n ℤ (cayDet n ℤ ^ s) =
      C (eval onePt (cayOp n ℤ (cayDet n ℤ ^ s))) * cayDet n ℤ ^ s := by
  apply MvPolynomial.funext
  intro x
  have h1 := cayOp_linSub (Matrix.of fun i j => x (i, j)) (cayDet n ℤ ^ s)
  rw [map_pow (linSub (Matrix.of fun i j => x (i, j))), linSub_cayDet, mul_pow,
    ← map_pow (C : ℤ →+* MvPolynomial (Fin n × Fin n) ℤ), MvPolynomial.C_mul', map_smul,
    ← MvPolynomial.C_mul'] at h1
  have h3 := congrArg (eval onePt) h1
  simp only [map_mul, map_pow, eval_C, eval_onePt_linSub] at h3
  simp only [map_mul, map_pow, eval_C, eval_cayDet]
  linear_combination -1 * h3
end ReciprocityTheory.PGsh
