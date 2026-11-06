-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.completionEmbedding_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:59.90318+00:00
-- url     : https://prove2.me/submissions/c49cb501-966f-4ceb-89ea-fd1820a604ef

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
    Function.Injective P.completionEmbedding :=
  P.completionEmbedding.injective
end QEC.Coding.AlgebraicGeometry.GlobalPlace
