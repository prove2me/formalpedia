-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGrowth.SharedZPath.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:39:28.560921+00:00
-- url     : https://prove2.me/submissions/7f6464d9-97b0-4479-9252-2667b1bc83c9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGrowth

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGrowth
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26RXDifferentialMasks
open BDL26FiniteAlternatingCore MultiscaleDecoder BDL26IndexedDecoder
namespace QEC.Coding.BDL26RXIncidenceHullGrowth
namespace SharedZPath
theorem _root_.solution {P : TannerSquarePresentation} {q r t : P.Q}
    (first : SharedZPath P q r) (second : SharedZPath P r t) : SharedZPath P q t := by
  induction second with
  | refl => exact first
  | snoc path z left right ih => exact .snoc ih z left right
end SharedZPath
end QEC.Coding.BDL26RXIncidenceHullGrowth
