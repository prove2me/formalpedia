-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.pslRight_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:29.210811+00:00
-- url     : https://prove2.me/submissions/7c20d4aa-84f7-4a62-89d0-4d6f5c609407

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionPSLGenerators
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_toPGL_pslLeft
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_toPGL_pslRight
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_toPGL_liftToPSL
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_indexedRight_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.toPGL_pslLeft
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.toPGL_pslRight

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
variable (f : F →+* K) (epsilon : F) (r y s i : K)
  (hEpsilon : epsilon ≠ 0) (hRoot : r ^ 2 = f epsilon)
  (hR : r ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
  (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
  (hRatio : s ^ 2 = y / (1 + y)) (hI : i ^ 2 = -1)
local notation "E" => projectiveMatrixEquivOfRoot (f epsilon) r y hRoot hR hOne hTwo
local notation "L" => indexedLeft f epsilon y hTwoF hY hOne hTwo
local notation "R" => indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo
include hEpsilon hRatio hI
local notation "PL" => pslLeft f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
local notation "PR" => pslRight f epsilon r y s i hEpsilon hRoot hR hTwoF
  hY hOne hTwo hRatio hI
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution : Function.Injective PR := by
  intro a b h
  have hImage := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  simp only [toPGL_pslRight] at hImage
  exact indexedRight_injective f epsilon y hEpsilon hTwoF hY hOne hTwo
    ((E).injective hImage)
end QEC.Coding.ExpanderCodes.QuaternionGenerators
