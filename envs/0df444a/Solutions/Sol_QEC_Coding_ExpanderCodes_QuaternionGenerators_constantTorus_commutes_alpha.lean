-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_commutes_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:34:55.769867+00:00
-- url     : https://prove2.me/submissions/08f29176-04d0-46db-bad7-c2859f71fc72

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (t : constantTorus f epsilon y) :
    (t : ProjectiveGroup (f epsilon) y) *
        projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) * t := by
  obtain ⟨a, ha⟩ := t.property
  rw [← ha]
  have hUnits : Units.map (coefficientEmbedding f epsilon y).toMonoidHom a *
        alphaUnit (f epsilon) y ((map_ne_zero f).mpr hEpsilon) =
      alphaUnit (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
        Units.map (coefficientEmbedding f epsilon y).toMonoidHom a := by
    apply Units.ext
    ext <;> simp [coefficientEmbedding, alpha]
  have hProjective := congrArg (QuotientGroup.mk' (Subgroup.center (Model (f epsilon) y)ˣ)) hUnits
  simpa [constantProjectiveMap, projectiveAlpha, QuotientGroup.mk_mul] using hProjective
end QEC.Coding.ExpanderCodes.QuaternionGenerators
