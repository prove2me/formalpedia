-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.evaluate_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:47:43.710674+00:00
-- url     : https://prove2.me/submissions/4f87c5e9-c963-4b67-bbec-d2bf9253a169

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.RationalPlace
theorem _root_.solution (Q : RationalPlace k F)
    (x : GlobalPlace.valuationRing Q.place) :
    Q.evaluate x = 0 ↔ x ∈ IsLocalRing.maximalIdeal (GlobalPlace.valuationRing Q.place) := by
  change Q.constantsEquiv.symm (GlobalPlace.residue Q.place x) = 0 ↔ _
  rw [Q.constantsEquiv.symm.map_eq_zero_iff,
    GlobalPlace.residue_eq_zero_iff]
end QEC.Coding.AlgebraicGeometry.RationalPlace
