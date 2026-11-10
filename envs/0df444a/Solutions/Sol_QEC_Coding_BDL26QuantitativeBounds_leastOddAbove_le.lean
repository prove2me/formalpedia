-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.leastOddAbove_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:18:27.678696+00:00
-- url     : https://prove2.me/submissions/63edf4fa-5267-47e4-a809-f53866d0753d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (threshold n : Nat) (hodd : n % 2 = 1) (hgt : threshold < n) :
    leastOddAbove threshold ≤ n := by
  unfold leastOddAbove
  omega
end QEC.Coding.BDL26QuantitativeBounds
