-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.SharedZPath.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:53:30.070861+00:00
-- url     : https://prove2.me/submissions/9d3c285e-f493-4edd-a668-5753bac50e71

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_trans
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
namespace SharedZPath
theorem _root_.solution {P : TannerSquarePresentation} {q r : P.Q}
    (path : SharedZPath P q r) : SharedZPath P r q := by
  induction path with
  | refl => exact .refl _
  | @snoc r t path z left right ih =>
      exact (SharedZPath.snoc (SharedZPath.refl (P := P) t) z right left).trans ih
end SharedZPath
end QEC.Coding.BDL26RXIncidenceHullGrowth
