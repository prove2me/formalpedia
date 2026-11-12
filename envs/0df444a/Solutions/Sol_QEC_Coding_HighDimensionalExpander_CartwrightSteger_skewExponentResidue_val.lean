-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewExponentResidue_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:19:46.200697+00:00
-- url     : https://prove2.me/submissions/65308f45-f106-4fcd-b7cc-acfc3ad3702e

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_LaurentEvaluation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (r : Rank) (n : ℤ) :
    ((skewExponentResidue r n : Fin r.matrixRank) : ℕ) =
      (n % (r.matrixRank : ℤ)).toNat := rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
