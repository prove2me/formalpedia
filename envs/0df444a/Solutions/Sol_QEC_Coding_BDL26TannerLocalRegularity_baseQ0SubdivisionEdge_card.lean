-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionEdge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:02.696765+00:00
-- url     : https://prove2.me/submissions/ae836ad1-950b-4de0-be95-d6928840e99a

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
      (0 : BaseQubit) scaleFive) = 2 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
