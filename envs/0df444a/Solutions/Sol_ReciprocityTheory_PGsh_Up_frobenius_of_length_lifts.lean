-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.frobenius_of_length_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:16.219244+00:00
-- url     : https://prove2.me/submissions/a7a1e9ff-5eb0-4ba8-9403-ea589d36a222

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EqZeroOfIsoZero
import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_ReciprocityTheory_DualLattices_MonomialsSpanOfProdEq
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
import Definitions.Def_ReciprocityTheory_DualLattices_RankEqRankOfPermAndZero
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_FrobeniusBlock
import Definitions.Def_ReciprocityTheory_DualLattices_SumX
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroup
import Definitions.Def_ReciprocityTheory_DualLattices_FrobeniusOfGroupDivisorsRank
import Theorems.Thm_ReciprocityTheory_PGsh_Up_core_of
import Theorems.Thm_ReciprocityTheory_PGsh_Up_lifts_of
import Theorems.Thm_ReciprocityTheory_PGsh_Up_unramifiedCokernelLength_of_length_eigenLengthProduct


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hLen : LenIdStatement) (hEx : LenExStatement) (hTot : EigenLengthProductStatement)
    (hG : EmbeddingSeparatingGroupStatement) (hE : EigenElementaryDivisorStatement) (hR : EigenRankStatement)
    (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) : UnramifiedCokernelLengthStatement :=
  unramifiedCokernelLength_of_length_eigenLengthProduct hLen hEx hTot (core_of (lifts_of hG hE hR) hB hF)
end ReciprocityTheory.PGsh.Up
