-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:45:09.809618+00:00
-- url     : https://prove2.me/submissions/50da8160-4b28-407f-a827-13564d630cb1

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (P : GlobalPlace k F) (a : k) :
    ((constantsToValuationRing P a : valuationRing P) : F) = algebraMap k F a :=
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
