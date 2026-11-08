-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.base_boundedValence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:43:38.766158+00:00
-- url     : https://prove2.me/submissions/9f2eafe7-0806-40a7-ae35-27eed2270d97

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution : BoundedValence baseTannerSquarePresentation := by
  unfold BoundedValence
  decide
end QEC.Coding.BDL26BoundedValence
