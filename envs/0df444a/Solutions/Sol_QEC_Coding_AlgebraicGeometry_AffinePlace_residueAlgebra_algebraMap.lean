-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.residueAlgebra_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:41.194209+00:00
-- url     : https://prove2.me/submissions/afb890e7-9b2b-4e59-b6a1-a67022a2962a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (P : carrier k F) :
    letI : Algebra k (residueField k F P) := residueAlgebra k F P
    algebraMap k (residueField k F P) = constantsToResidue k F P :=
  rfl
end QEC.Coding.AlgebraicGeometry.AffinePlace
