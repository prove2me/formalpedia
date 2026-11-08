-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ4DoubleCylinderVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:33:32.845183+00:00
-- url     : https://prove2.me/submissions/406b897d-b89e-4f4e-8a33-f49aa0dc59aa

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
    Fintype.card (QDoubleCylinderVertex baseTannerSquarePresentation
      (4 : BaseQubit) scaleFive) = 10 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
