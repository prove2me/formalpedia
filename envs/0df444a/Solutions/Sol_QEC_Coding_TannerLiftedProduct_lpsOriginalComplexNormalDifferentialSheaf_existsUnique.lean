-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalDifferentialSheaf_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:55:23.014771+00:00
-- url     : https://prove2.me/submissions/75a2e99a-7775-4a1b-baad-566f06de2092

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeDifferentialSheafDerivation_existsUnique


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (M : Scheme.Modules X)
    (d : ((Scheme.Modules.toPresheafOfModules X).obj M).Derivation'
      (schemeConstantPresheafMap X (CommRingCat.of ℂ)
        (lpsOriginalComplexNormalGlobalConstantMap N hpos))) :
    ∃! f : lpsOriginalComplexNormalDifferentialSheaf N hpos ⟶ M,
      (lpsOriginalComplexNormalDifferentialSheafDerivation N hpos).postcomp
        ((Scheme.Modules.toPresheafOfModules X).map f) = d :=
  schemeDifferentialSheafDerivation_existsUnique X (CommRingCat.of ℂ)
    (lpsOriginalComplexNormalGlobalConstantMap N hpos) M d
end QEC.Coding.TannerLiftedProduct
