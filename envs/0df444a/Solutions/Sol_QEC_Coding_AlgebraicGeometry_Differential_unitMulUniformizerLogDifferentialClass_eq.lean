-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.unitMulUniformizerLogDifferentialClass_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:19:04.710795+00:00
-- url     : https://prove2.me/submissions/7f12097e-d88a-4b57-8244-1e9e542ccad3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalLogarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) (u : P.valuationRingˣ) :
    Submodule.Quotient.mk
        (unitMulUniformizerLogDifferential (k := k) (F := F) P u) =
      uniformizerLogDifferentialClass (k := k) (F := F) P := by
  apply (Submodule.Quotient.eq
    (regularDifferentialSubmoduleOfSimplePole P)).2
  change logarithmicDifferential (k := k) (F := F)
      ((u : F) * (P.uniformizerInValuationRing : F)) -
        logarithmicDifferential (k := k) (F := F)
          (P.uniformizerInValuationRing : F) ∈ localDifferentialLattice P
  have hu : (u : F) ≠ 0 := by
    intro hzero
    apply Units.ne_zero u
    apply Subtype.ext
    exact hzero
  have hpi : (P.uniformizerInValuationRing : F) ≠ 0 := by
    simpa [GlobalPlace.uniformizerInValuationRing, localParameter] using
      localParameter_ne_zero (k := k) (F := F) P
  rw [logarithmicDifferential_mul (k := k) (F := F) _ _ hu hpi,
    add_sub_cancel_right]
  exact logarithmicDifferential_mem_localDifferentialLattice_of_unit
    (k := k) (F := F) P u
end QEC.Coding.AlgebraicGeometry.Differential
