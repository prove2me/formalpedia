-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarEdge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:46.575539+00:00
-- url     : https://prove2.me/submissions/c0aa2dd6-cf4e-4b82-992b-3aa850238261

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u
namespace QEC.Coding.BDL26TannerLocalRegularity
theorem _root_.solution :
    Fintype.card (QStarEdge baseTannerSquarePresentation (0 : BaseQubit)) = 1 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
