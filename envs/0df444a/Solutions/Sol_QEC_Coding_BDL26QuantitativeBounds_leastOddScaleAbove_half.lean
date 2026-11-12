-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:57:21.110117+00:00
-- url     : https://prove2.me/submissions/0d189e74-9e58-426f-8629-997fedc15435

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (threshold : ℝ) (hone : 1 ≤ threshold) :
    (leastOddScaleAbove threshold hone).half = (⌊threshold⌋₊ + 1) / 2 := by
  have h := (leastOddScaleAbove threshold hone).two_half_add_one
  change 2 * (leastOddScaleAbove threshold hone).half + 1 =
    2 * ((⌊threshold⌋₊ + 1) / 2) + 1 at h
  omega
end QEC.Coding.BDL26QuantitativeBounds
