-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentIntSupport_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:52:57.520764+00:00
-- url     : https://prove2.me/submissions/0251b6ed-46fe-46f9-a8ee-c0421e8608d8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    {f : CartwrightStegerSkewLaurentRing P r} (hf : f ≠ 0) :
    (skewLaurentIntSupport P r f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hs : f.support = ∅ := by
    apply Finset.map_eq_empty.mp
    exact hempty
  exact hf (SkewMonoidAlgebra.support_eq_empty.mp hs)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
