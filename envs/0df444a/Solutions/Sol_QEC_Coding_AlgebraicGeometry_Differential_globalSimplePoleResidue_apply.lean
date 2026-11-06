-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:35:48.62583+00:00
-- url     : https://prove2.me/submissions/8b84a9cd-cfe4-416c-abb1-04d2c5aa886f

import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (omega : Differential k F) (homega : IsGlobalSimplePole omega)
    (P : GlobalPlace k F) :
    globalSimplePoleResidue (k := k) (F := F) omega homega P =
      globalSimplePoleResidueCoefficient (k := k) (F := F) omega homega P :=
  rfl
end QEC.Coding.AlgebraicGeometry.Differential
