-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponent_eq_of_residue_eq_of_quotient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:28:02.400467+00:00
-- url     : https://prove2.me/submissions/057c0bda-7242-4b56-80ad-63b973b41bb9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewExponent_decomposition

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (r : Rank) {m n : ℤ}
    (hres : skewExponentResidue r m = skewExponentResidue r n)
    (hquot : skewExponentQuotient r m = skewExponentQuotient r n) :
    m = n := by
  rw [skewExponent_decomposition r m,
    skewExponent_decomposition r n, hquot, hres]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
