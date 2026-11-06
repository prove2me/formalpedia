-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.evaluateRegular_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:21.474453+00:00
-- url     : https://prove2.me/submissions/810c9daa-e334-449e-994b-a4e9adbf04fb

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.RationalPlace
theorem _root_.solution (Q : RationalPlace k F) (f : F)
    (hf : GlobalPlace.RegularAt Q.place f) :
    Q.evaluateRegular f hf = 0 ↔
      (⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩ :
        GlobalPlace.valuationRing Q.place) ∈
        IsLocalRing.maximalIdeal (GlobalPlace.valuationRing Q.place) := by
  exact Q.evaluate_eq_zero_iff _
end QEC.Coding.AlgebraicGeometry.RationalPlace
