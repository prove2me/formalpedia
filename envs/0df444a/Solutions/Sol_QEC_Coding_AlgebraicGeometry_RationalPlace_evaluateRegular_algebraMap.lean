-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.evaluateRegular_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:48.163876+00:00
-- url     : https://prove2.me/submissions/f746a640-91e8-4357-9e07-46c5de165270

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.RationalPlace
theorem _root_.solution (Q : RationalPlace k F) (a : k) :
    Q.evaluateRegular (algebraMap k F a) (Q.constants_regular a) = a := by
  change Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) = a
  exact Q.evaluate_constants a
end QEC.Coding.AlgebraicGeometry.RationalPlace
