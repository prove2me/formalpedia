-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ0DoubleCylinderVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:34:28.6753+00:00
-- url     : https://prove2.me/submissions/ed776afd-437d-4e2e-9bfa-14a38f19b221

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
      (0 : BaseQubit) scaleFive) = 6 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
