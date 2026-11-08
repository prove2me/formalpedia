-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ4StarEdge_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:00.766308+00:00
-- url     : https://prove2.me/submissions/9161c65d-ef51-4f11-997d-23424dd7f79b

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
    Fintype.card (QStarEdge baseTannerSquarePresentation (4 : BaseQubit)) = 2 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
