-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ0StarVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:29.159024+00:00
-- url     : https://prove2.me/submissions/8ffb1791-fca1-4d44-865f-202988a8e7b7

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
    Fintype.card (QStarVertex baseTannerSquarePresentation (0 : BaseQubit)) = 2 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
