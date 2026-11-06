-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepAbovePlace_order_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:53:41.70554+00:00
-- url     : https://prove2.me/submissions/f0e79d11-1261-4b4d-9251-d227fd8a3d44

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepIntegralRoot_multiplicity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem sourceStepAbovePlace_order_integral_eq_multiplicity
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1)
    {y : SourceStepIntegralClosure P x hx} (hy : y ≠ 0) :
    (sourceStepAbovePlace P x hx).order
        (algebraMap (SourceStepIntegralClosure P x hx)
          (SourceStepField P x hx) y) =
      (multiplicity (sourceStepUpperIdeal P x hx) (Ideal.span {y}) : ℤ) := by
  unfold sourceStepAbovePlace GlobalPlace.order
  rw [(sourceStepUpperHeightOne P x hx).valuation_of_algebraMap,
    (sourceStepUpperHeightOne P x hx).intValuation_eq_exp_neg_multiplicity hy,
    WithZero.log_exp]
  simp only [sourceStepUpperHeightOne]
  ring
private theorem sourceStepAbovePlace_order_reciprocalRoot
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepAbovePlace P x hx).order
      (sourceStepReciprocalRoot P x hx) = 1 := by
  change (sourceStepAbovePlace P x hx).order
    (algebraMap (SourceStepIntegralClosure P x hx)
      (SourceStepField P x hx) (sourceStepIntegralRoot P x hx)) = 1
  rw [sourceStepAbovePlace_order_integral_eq_multiplicity P x hx
      (sourceStepIntegralRoot_ne_zero P x hx),
    sourceStepIntegralRoot_multiplicity]
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
    (P : GlobalPlace F256 K) (x : K) (hx : P.order x = -1) :
    (sourceStepAbovePlace P x hx).order (sourceStepCoordinate P x hx) = -1 := by
  rw [sourceStepCoordinate, GlobalPlace.order_inv,
    sourceStepAbovePlace_order_reciprocalRoot]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
