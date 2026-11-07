-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.fullRowRankCosetLeaderMatrix_isCosetLeader
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:52.886337+00:00
-- url     : https://prove2.me/submissions/9ae41544-a28c-4068-8e5e-a7c3465d1c9e

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_cosetLeaderMatrix_isCosetLeader

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
    (z : Matrix W R F) (i : W) :
    IsCosetLeader h (z i) (row (fullRowRankCosetLeaderMatrix h hRank z) i) := by
  exact cosetLeaderMatrix_isCosetLeader h z
    (fun i => fullRowRankPreimage h hRank (z i))
    (fun i => fullRowRankPreimage_syndrome h hRank (z i)) i
end QEC.Coding.ProductExpansion
