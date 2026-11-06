-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierAbovePlace_order_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:56:04.205891+00:00
-- url     : https://prove2.me/submissions/ca3c9bcc-0a72-48c9-937e-435111891cd9

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStep
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierIntegralRoot_multiplicity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem quadraticArtinSchreierAbovePlace_order_integral_eq_multiplicity
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1)
    {z : QuadraticArtinSchreierIntegralClosure P a ha} (hz : z ≠ 0) :
    (quadraticArtinSchreierAbovePlace P a ha).order
        (algebraMap (QuadraticArtinSchreierIntegralClosure P a ha)
          (QuadraticArtinSchreierField P a ha) z) =
      (multiplicity (quadraticArtinSchreierUpperIdeal P a ha)
        (Ideal.span {z}) : ℤ) := by
  unfold quadraticArtinSchreierAbovePlace GlobalPlace.order
  rw [(quadraticArtinSchreierUpperHeightOne P a ha).valuation_of_algebraMap,
    (quadraticArtinSchreierUpperHeightOne P a ha).intValuation_eq_exp_neg_multiplicity hz,
    WithZero.log_exp]
  simp only [quadraticArtinSchreierUpperHeightOne]
  ring
private theorem quadraticArtinSchreierAbovePlace_order_reciprocalRoot
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierAbovePlace P a ha).order
      (quadraticArtinSchreierReciprocalRoot P a ha) = 1 := by
  change (quadraticArtinSchreierAbovePlace P a ha).order
    (algebraMap (QuadraticArtinSchreierIntegralClosure P a ha)
      (QuadraticArtinSchreierField P a ha)
      (quadraticArtinSchreierIntegralRoot P a ha)) = 1
  rw [quadraticArtinSchreierAbovePlace_order_integral_eq_multiplicity
      P a ha (quadraticArtinSchreierIntegralRoot_ne_zero P a ha),
    quadraticArtinSchreierIntegralRoot_multiplicity]
  norm_num
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) :
    (quadraticArtinSchreierAbovePlace P a ha).order
      (quadraticArtinSchreierCoordinate P a ha) = -1 := by
  rw [quadraticArtinSchreierCoordinate, GlobalPlace.order_inv,
    quadraticArtinSchreierAbovePlace_order_reciprocalRoot]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
