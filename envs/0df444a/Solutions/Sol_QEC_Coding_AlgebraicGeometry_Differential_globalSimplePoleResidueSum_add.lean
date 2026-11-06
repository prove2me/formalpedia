-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:52.137498+00:00
-- url     : https://prove2.me/submissions/72168e07-3a3d-427f-a536-bf0ee34108d8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_add
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
    globalSimplePoleResidueSum (k := k) (F := F) (omega + eta)
        (homega.add heta) =
      globalSimplePoleResidueSum (k := k) (F := F) omega homega +
        globalSimplePoleResidueSum (k := k) (F := F) eta heta := by
  rw [globalSimplePoleResidueSum, globalSimplePoleResidue_add]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
end QEC.Coding.AlgebraicGeometry.Differential
