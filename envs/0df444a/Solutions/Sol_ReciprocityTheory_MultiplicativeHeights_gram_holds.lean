-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gram_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:00.508124+00:00
-- url     : https://prove2.me/submissions/770b494a-d500-41e0-972f-be4431b7c05b

import Definitions.Def_ReciprocityTheory_SemistableReduction_DetGramEqProdGramSchmidt
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex
import Definitions.Def_ReciprocityTheory_SemistableReduction_GramOfLinearOrder
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gram_of_linearOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) : GramStatement := by
  unfold GramStatement
  intro ι _ _ F S hF
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  convert gram_of_linearOrder hBasic hLex hL2 F S hF
end ReciprocityTheory.MultiplicativeHeights
