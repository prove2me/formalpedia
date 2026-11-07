-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.cosetLeaderMatrix_productKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:47.663088+00:00
-- url     : https://prove2.me/submissions/4f3d6514-c88a-4ed4-a9db-ae98487e6e44

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_mul_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (z : Matrix W R F) (x₀ : Matrix W W F)
    (hx₀ : ∀ i, h.mulVec (row x₀ i) = z i)
    (hz : h' * z = 0) :
    ProductKernel h h' (cosetLeaderMatrix h z x₀ hx₀) := by
  unfold ProductKernel
  rw [Matrix.mul_assoc, cosetLeaderMatrix_mul_transpose h z x₀ hx₀, hz]
end QEC.Coding.ProductExpansion
