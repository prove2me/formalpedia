-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:29.255917+00:00
-- url     : https://prove2.me/submissions/3a8a62af-a279-4a4e-a5e3-868ec32b89ca

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_mul_transpose

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq W]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (hRank : h.rank = Fintype.card R)
    (z : Matrix W R F) :
    fullRowRankCosetLeaderMatrix h hRank z * h.transpose = z := by
  exact cosetLeaderMatrix_mul_transpose h z
    (fun i => fullRowRankPreimage h hRank (z i))
    (fun i => fullRowRankPreimage_syndrome h hRank (z i))
end QEC.Coding.ProductExpansion
