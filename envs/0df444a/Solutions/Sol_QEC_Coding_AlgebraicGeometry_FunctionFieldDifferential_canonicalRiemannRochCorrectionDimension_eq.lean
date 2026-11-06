-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalRiemannRochCorrectionDimension_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:47:01.651229+00:00
-- url     : https://prove2.me/submissions/331399a0-68b0-4409-9469-32fa16e3a046

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_CanonicalCorrection
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_canonicalDivisors_differ_by_principal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_principal_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
variable [Algebra (Polynomial k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L)
    (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (GlobalPlace.riemannRochSubmodule (K - G))]
    [FiniteDimensional k (GlobalPlace.riemannRochSubmodule (L - G))] :
    GlobalPlace.riemannRochDimension (K - G) =
      GlobalPlace.riemannRochDimension (L - G) := by
  rcases canonicalDivisors_differ_by_principal (k := k) (F := F) hK hL with
    ⟨u, hL⟩
  have hshift :
      L - G =
        GlobalPlace.principalDivisor (k := k) (F := F) u + (K - G) := by
    rw [hL]
    abel
  letI : FiniteDimensional k
      (GlobalPlace.riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + (K - G))) := by
    rw [← hshift]
    infer_instance
  have hdimension :=
    GlobalPlace.riemannRochDimension_principal_add
      (k := k) (F := F) u (K - G)
  simpa only [← hshift] using hdimension.symm
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
