-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionEdge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:06.334417+00:00
-- url     : https://prove2.me/submissions/8f786f65-4493-4074-bd42-f8f87b1ced53

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
    Fintype.card (QSubdivisionEdge baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 4 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
