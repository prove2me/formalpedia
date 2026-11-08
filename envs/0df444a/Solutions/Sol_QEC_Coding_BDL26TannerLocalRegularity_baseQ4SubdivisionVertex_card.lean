-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ4SubdivisionVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:50.321588+00:00
-- url     : https://prove2.me/submissions/17a8621a-cd34-4911-b8c8-327dfceb26af

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
    Fintype.card (QSubdivisionVertex baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 5 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
