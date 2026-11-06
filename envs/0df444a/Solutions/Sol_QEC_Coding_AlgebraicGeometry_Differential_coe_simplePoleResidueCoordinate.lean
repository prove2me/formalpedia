-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_simplePoleResidueCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:46.663658+00:00
-- url     : https://prove2.me/submissions/311ce634-fef7-4dec-b08c-80c80e56cf17

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (P : GlobalPlace k F)
    (omega : simplePoleDifferentialLattice P) :
    ((simplePoleResidueCoordinate (k := k) (F := F) P omega :
      P.valuationRing) : F) =
      (P.uniformizerInValuationRing : F) *
        functionFieldDifferentialCoordinate (k := k) (F := F)
          (omega : Differential k F) *
        (functionFieldDerivation (k := k) (F := F)
          (P.uniformizerInValuationRing : F))⁻¹ :=
  rfl
end QEC.Coding.AlgebraicGeometry.Differential
