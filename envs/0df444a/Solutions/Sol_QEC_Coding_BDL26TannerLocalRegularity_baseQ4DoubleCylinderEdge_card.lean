-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderEdge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:23.182905+00:00
-- url     : https://prove2.me/submissions/52de6a84-963c-46c2-93dc-456a4d810a5e

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
    Fintype.card (QDoubleCylinderEdge baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 10 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
