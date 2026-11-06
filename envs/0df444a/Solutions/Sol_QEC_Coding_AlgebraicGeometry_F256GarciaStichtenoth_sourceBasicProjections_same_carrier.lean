-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicProjections_same_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:27.181276+00:00
-- url     : https://prove2.me/submissions/2c23b181-9994-4947-aa54-9ff298352cba

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_LiteralSourceStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open IntermediateField
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem adjoin_inv_eq_adjoin
    {k E : Type*} [_root_.Field k] [_root_.Field E] [Algebra k E] (x : E) :
    k⟮x⁻¹⟯ = k⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z = x⁻¹ := Set.mem_singleton_iff.mp hz
    subst z
    exact (k⟮x⟯).inv_mem (IntermediateField.subset_adjoin k _ (Set.mem_singleton x))
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    have hmem :=
      (k⟮x⁻¹⟯).inv_mem (IntermediateField.subset_adjoin k _ (Set.mem_singleton x⁻¹))
    simp only [inv_inv] at hmem
    exact hmem
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    ((SourceBasicForwardField i)⟮sourceDistinguishedCoordinate (i + 1)⟯).restrictScalars F256 =
      ((SourceBasicReverseField i)⟮
        sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹)⟯).restrictScalars F256 := by
  change ((F256⟮sourceRecursionEmbedding i (sourceDistinguishedCoordinate i)⟯)⟮
      sourceDistinguishedCoordinate (i + 1)⟯).restrictScalars F256 =
    ((F256⟮(sourceDistinguishedCoordinate (i + 1))⁻¹⟯)⟮
      sourceRecursionEmbedding i ((sourceDistinguishedCoordinate i)⁻¹)⟯).restrictScalars F256
  rw [IntermediateField.restrictScalars_adjoin_eq_sup,
    IntermediateField.restrictScalars_adjoin_eq_sup, map_inv₀,
    adjoin_inv_eq_adjoin, adjoin_inv_eq_adjoin, sup_comm]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
