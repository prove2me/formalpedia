-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:30.3443+00:00
-- url     : https://prove2.me/submissions/c3bb0e52-2730-4b07-be6e-1e741edfc0bd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_Nonnegative_add


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (omega eta : Differential k F)
    (homega : IsGlobalSimplePole (k := k) (F := F) omega)
    (heta : IsGlobalSimplePole (k := k) (F := F) eta) :
    globalSimplePoleResidue (k := k) (F := F) (omega + eta)
        (homega.add heta) =
      globalSimplePoleResidue (k := k) (F := F) omega homega +
        globalSimplePoleResidue (k := k) (F := F) eta heta := by
  ext P
  rw [globalSimplePoleResidue_apply, Finsupp.add_apply,
    globalSimplePoleResidue_apply, globalSimplePoleResidue_apply]
  exact simplePoleTraceResidue_add (k := k) (F := F) P omega eta
    (homega P) (heta P)
end QEC.Coding.AlgebraicGeometry.Differential
