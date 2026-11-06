-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.evaluate_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:44:16.480328+00:00
-- url     : https://prove2.me/submissions/cf55f7ff-08c8-48a6-b5fb-28f0f5dc4a8e

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.RationalPlace
theorem _root_.solution (Q : RationalPlace k F) (a : k) :
    Q.evaluate (GlobalPlace.constantsToValuationRing Q.place a) = a := by
  change Q.constantsEquiv.symm (GlobalPlace.constantsToResidue Q.place a) = a
  rw [← Q.constantsEquiv_apply a, Q.constantsEquiv.symm_apply_apply]
end QEC.Coding.AlgebraicGeometry.RationalPlace
