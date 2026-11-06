-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.constantsToResidue_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:03:41.050915+00:00
-- url     : https://prove2.me/submissions/f649c2bf-84c2-475f-9929-a4bb79241e04

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.RationalPlace
theorem _root_.solution (Q : RationalPlace k F) :
    Function.Bijective (GlobalPlace.constantsToResidue Q.place) := by
  constructor
  · intro a b hab
    apply Q.constantsEquiv.injective
    simpa only [Q.constantsEquiv_apply] using hab
  · intro x
    obtain ⟨a, ha⟩ := Q.constantsEquiv.surjective x
    refine ⟨a, ?_⟩
    rw [← Q.constantsEquiv_apply a]
    exact ha
end QEC.Coding.AlgebraicGeometry.RationalPlace
