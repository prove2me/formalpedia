-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartDifferentialRestrictionIso_derivation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:47:05.598634+00:00
-- url     : https://prove2.me/submissions/76502ba6-1c49-4f27-8ac3-be2a5a72ebf6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SchemeRestriction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialRestriction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialRestrictionIso_derivation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "c" => lpsOriginalComplexNormalGlobalConstantMap N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalChartDifferentialRestrictionOpenImmersion
attribute [local instance] lpsOriginalZeroChartDifferentialAlgebra
  lpsOriginalInfinityChartDifferentialAlgebra lpsOriginalZeroChartDifferentialSMul
  lpsOriginalZeroChartDifferentialModule lpsOriginalZeroChartDifferentialSMulComm
  lpsOriginalZeroChartOmegaSMul lpsOriginalZeroChartOmegaModule
  lpsOriginalInfinityChartDifferentialSMul lpsOriginalInfinityChartDifferentialModule
  lpsOriginalInfinityChartDifferentialSMulComm lpsOriginalInfinityChartOmegaSMul
  lpsOriginalInfinityChartOmegaModule
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (b : Bool) :
    (schemeDifferentialSheafDerivation (lpsOriginalComplexNormalSchemeChart N hpos b)
      (CommRingCat.of ℂ) (c ≫ (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop)).postcomp
      ((Scheme.Modules.toPresheafOfModules (lpsOriginalComplexNormalSchemeChart N hpos b)).map
        (lpsOriginalComplexNormalChartDifferentialRestrictionIso N hpos b).hom) =
    schemeRestrictedDifferentialSheafDerivation (lpsOriginalComplexNormalGluedChartMap N hpos b)
      (CommRingCat.of ℂ) c :=
  schemeDifferentialRestrictionIso_derivation (lpsOriginalComplexNormalGluedChartMap N hpos b)
    (CommRingCat.of ℂ) c
end QEC.Coding.TannerLiftedProduct
