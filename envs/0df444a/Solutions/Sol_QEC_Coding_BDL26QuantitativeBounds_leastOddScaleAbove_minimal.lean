-- Prove2me | solution 1 for QEC.Coding.BDL26QuantitativeBounds.leastOddScaleAbove_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:56:42.565361+00:00
-- url     : https://prove2.me/submissions/e4ea4e33-0dbb-40dc-abfe-de87e638079a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_leastOddAbove_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26QuantitativeBounds
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26DecodingGraph
namespace QEC.Coding.BDL26QuantitativeBounds
theorem _root_.solution (threshold : ℝ) (hone : 1 ≤ threshold)
    (n : Nat) (hodd : n % 2 = 1) (hgt : threshold < n) :
    (leastOddScaleAbove threshold hone).ell ≤ n :=
  leastOddAbove_le _ n hodd ((Nat.floor_lt (by linarith)).mpr hgt)
end QEC.Coding.BDL26QuantitativeBounds
