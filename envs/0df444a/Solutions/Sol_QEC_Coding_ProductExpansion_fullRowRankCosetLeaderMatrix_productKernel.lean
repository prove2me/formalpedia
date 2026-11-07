-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_productKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:56.029016+00:00
-- url     : https://prove2.me/submissions/bd2a33d5-a930-4f45-8ce1-64f6142127f2

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_fullRowRankCosetLeaderMatrix_mul_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (hRank : h.rank = Fintype.card R) (z : Matrix W R F)
    (hz : h' * z = 0) :
    ProductKernel h h' (fullRowRankCosetLeaderMatrix h hRank z) := by
  unfold ProductKernel
  rw [Matrix.mul_assoc,
    fullRowRankCosetLeaderMatrix_mul_transpose h hRank z, hz]
end QEC.Coding.ProductExpansion
