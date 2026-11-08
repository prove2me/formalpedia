-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.baseQ0SubdivisionVertex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:35.722646+00:00
-- url     : https://prove2.me/submissions/1b0c98a1-1483-4509-8dc9-f1331b70bb7d

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
      (0 : BaseQubit) scaleFive) = 3 := by
  decide +kernel
end QEC.Coding.BDL26TannerLocalRegularity
