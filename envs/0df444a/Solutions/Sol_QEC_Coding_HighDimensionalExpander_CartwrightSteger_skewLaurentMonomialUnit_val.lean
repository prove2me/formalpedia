-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:51:25.342174+00:00
-- url     : https://prove2.me/submissions/b330c7be-808b-4574-9575-b31c103781e8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
import Mathlib.Algebra.SkewMonoidAlgebra.Support
import Mathlib.Algebra.Ring.Action.End
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (c : (ConstantExtension P r)ˣ) (n : ℤ) :
    (skewLaurentMonomialUnit P r c n :
      CartwrightStegerSkewLaurentRing P r) =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd n)
        (c : ConstantExtension P r) := rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
