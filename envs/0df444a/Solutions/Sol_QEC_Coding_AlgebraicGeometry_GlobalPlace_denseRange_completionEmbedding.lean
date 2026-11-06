-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.denseRange_completionEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:57.801242+00:00
-- url     : https://prove2.me/submissions/e8ba9c95-9c0b-4bd5-b14e-10a8479c3201

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Valued.ValuedField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (P : GlobalPlace k F) :
    DenseRange P.completionEmbedding :=
  UniformSpace.Completion.denseRange_coe.comp
    (WithVal.equiv P.valuation).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
