-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_verticalUnramified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:39:14.323795+00:00
-- url     : https://prove2.me/submissions/cb6b614d-3ad1-4764-8b8b-c2f70a4e4069

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.Locus
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalVerticalUnramified
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_unramifiedAt_of_localization_disjoint
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_verticalDenominatorsDisjoint
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussNormalization_etale
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroGauss_localization


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
local notation "K" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "C" => integralClosure (Polynomial ℤ) K
local notation "D" => integralClosure (LPSOriginalGaussBase p) K
include hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hpN : ¬ p ∣ N) (q : Ideal C) [q.IsPrime] (hq : q.height = 1)
    (hpq : (p : C) ∈ q) : Algebra.IsUnramifiedAt (Polynomial ℤ) q := by
  let instGK : Algebra (LPSOriginalGaussBase p) K :=
    (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  let := lpsOriginalGaussBase_scalarTower N hN p
  let instRD : Algebra (Polynomial ℤ) D :=
    ((algebraMap (LPSOriginalGaussBase p) D).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p))).toAlgebra
  let : SMul (Polynomial ℤ) D := instRD.toSMul
  let : IsScalarTower (Polynomial ℤ) (LPSOriginalGaussBase p) D :=
    .of_algebraMap_eq' rfl
  let instCD : Algebra C D :=
    (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower (Polynomial ℤ) C D :=
    .of_algebraMap_eq' (by
      apply RingHom.ext
      intro f
      apply Subtype.ext
      exact lpsOriginalGaussBaseToGeneratedField_base N hN p f)
  let M := Algebra.algebraMapSubmonoid C (lpsOriginalGaussPrime p).primeCompl
  let : IsLocalization M D := lpsOriginalIntegerNormalZeroGauss_localization N hN p
  let : Algebra.FormallyUnramified (Polynomial ℤ) (LPSOriginalGaussBase p) :=
    Algebra.FormallyUnramified.of_isLocalization (lpsOriginalGaussPrime p).primeCompl
  let : Algebra.Etale (LPSOriginalGaussBase p) D :=
    lpsOriginalGaussNormalization_etale N hN p hpN
  let : Algebra.FormallyUnramified (Polynomial ℤ) D :=
    Algebra.FormallyUnramified.comp (Polynomial ℤ) (LPSOriginalGaussBase p) D
  exact QEC.Coding.AlgebraicGeometry.unramifiedAt_of_localization_disjoint
    («D» := D) M q (lpsOriginalNormalZero_verticalDenominatorsDisjoint N hN p q hq hpq)
end QEC.Coding.TannerLiftedProduct
