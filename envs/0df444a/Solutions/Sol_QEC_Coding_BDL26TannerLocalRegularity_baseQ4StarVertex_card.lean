-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:48.430625+00:00
-- url     : https://prove2.me/submissions/269a5f7c-55cd-462a-9b41-3b95b771a575

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
    Fintype.card (QStarVertex baseTannerSquarePresentation (4 : BaseQubit)) = 3 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
