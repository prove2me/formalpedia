-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreier_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:30.803112+00:00
-- url     : https://prove2.me/submissions/31f05140-cae3-4d48-8dc2-be69fe32f502

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_regularQuadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreierDifferentIdeal_eq_top
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_regularQuadraticArtinSchreierIntegralRoot

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    (IsLocalRing.maximalIdeal P.valuationRing).ramificationIdx'
      (regularQuadraticArtinSchreierUpperIdeal P b hirr) = 1 := by
  let O := P.valuationRing
  let C := RegularQuadraticArtinSchreierIntegralClosure P b hirr
  let L := RegularQuadraticArtinSchreierField P b hirr
  let Q : Ideal C := regularQuadraticArtinSchreierUpperIdeal P b hirr
  letI : IsDiscreteValuationRing O :=
    P.valuationRing_isDiscreteValuationRing
  letI : Algebra (FractionRing O) (FractionRing C) :=
    FractionRing.liftAlgebra _ _
  letI : Algebra.IsSeparable (FractionRing O) (FractionRing C) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv O K).symm.toRingEquiv
      (FractionRing.algEquiv C L).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv O K).symm
      (FractionRing.algEquiv C L).symm x
  letI : Q.IsPrime :=
    (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).isPrime
  have hQ_ne_bot : Q ≠ ⊥ :=
    (regularQuadraticArtinSchreierUpperHeightOne P b hirr).ne_bot
  have hQ_ne_top : Q ≠ ⊤ :=
    (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).ne_top
  have hnotdvd : ¬ Q ∣ differentIdeal O C := by
    rw [regularQuadraticArtinSchreierDifferentIdeal_eq_top]
    intro hdvd
    apply hQ_ne_top
    exact top_unique (Ideal.dvd_iff_le.mp hdvd)
  have hunramified : Algebra.IsUnramifiedAt O Q :=
    (not_dvd_differentIdeal_iff (A := O) (B := C)).mp hnotdvd
  letI : Algebra.IsUnramifiedAt O Q := hunramified
  letI : Q.LiesOver (IsLocalRing.maximalIdeal O) :=
    regularQuadraticArtinSchreierUpperIdeal_liesOver P b hirr
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal O)
    Q (IsDiscreteValuationRing.not_a_field O)]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := O) (p := Q)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
