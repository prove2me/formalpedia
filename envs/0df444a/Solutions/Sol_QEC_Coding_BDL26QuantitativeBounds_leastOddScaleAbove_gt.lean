-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:18:39.761442+00:00
-- url     : https://prove2.me/submissions/e7b8e69e-6120-4bd1-aa26-1884d00c934e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (threshold : ℝ) (hone : 1 ≤ threshold) :
    threshold < (leastOddScaleAbove threshold hone).ell :=
  (Nat.floor_lt (by linarith)).mp (leastOddAbove_gt _)
end QEC.Coding.BDL26QuantitativeBounds
