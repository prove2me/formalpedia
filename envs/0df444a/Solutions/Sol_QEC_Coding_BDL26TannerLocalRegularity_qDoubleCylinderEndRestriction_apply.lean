-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.qDoubleCylinderEndRestriction_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:22.962226+00:00
-- url     : https://prove2.me/submissions/c12336a4-39b6-4a06-b742-ad6cf6e64b40

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
theorem _root_.solution
    (P : TannerSquarePresentation) (q : P.Q) (S : OddScale) (endIndex : Two)
    (word : Word Field (QDoubleCylinderVertex P q S))
    (vertex : QSubdivisionVertex P q S) :
    qDoubleCylinderEndRestriction P q S endIndex word vertex =
      word (endIndex, vertex) := rfl
end QEC.Coding.BDL26TannerLocalRegularity
