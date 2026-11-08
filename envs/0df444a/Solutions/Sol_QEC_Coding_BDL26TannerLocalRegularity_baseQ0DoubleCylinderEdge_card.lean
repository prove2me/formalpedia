-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderEdge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:21.069308+00:00
-- url     : https://prove2.me/submissions/0698e559-2c89-47d8-88c4-76ecb17b32ed

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
      (0 : BaseQubit) scaleFive) = 5 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
