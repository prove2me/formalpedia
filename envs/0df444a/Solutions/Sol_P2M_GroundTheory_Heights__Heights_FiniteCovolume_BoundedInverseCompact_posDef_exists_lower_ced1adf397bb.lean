-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_posDef_exists_lower_ced1adf397bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:16.165887+00:00
-- url     : https://prove2.me/submissions/b63bd891-9bd2-471d-94e7-a97d2dd8c195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.BoundedInverseCompact
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.BoundedInverseCompact
theorem _root_.solution {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → ℂ, c * ‖y‖ ^ 2 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := by
  set f : (ι → ℂ) → ℝ := fun y => (star y ⬝ᵥ (P *ᵥ y)).re with hf
  have hscale : ∀ (r : ℝ) (y : ι → ℂ), f (r • y) = r ^ 2 * f y := by
    intro r y
    simp only [hf, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
      Complex.smul_re]
    ring
  have hunit : ∀ y : ι → ℂ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  have hrecover : ∀ y : ι → ℂ, y ≠ 0 → f y = ‖y‖ ^ 2 * f (‖y‖⁻¹ • y) := by
    intro y hy
    rw [hscale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_pow,
      one_mul]
  by_cases hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty
  · have hcont : Continuous f := by simp only [hf]; fun_prop
    obtain ⟨y0, hy0, hmin⟩ :=
      (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
    have hy0ne : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    refine ⟨f y0, by simpa [hf] using hP.re_dotProduct_pos hy0ne, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp [hf]
    · change f y0 * ‖y‖ ^ 2 ≤ f y
      rw [hrecover y hy, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hunit y hy)) (sq_nonneg _)
  · refine ⟨1, one_pos, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp
    · exact absurd ⟨_, hunit y hy⟩ hne
end GroundTheory.Heights₂.Heights.FiniteCovolume.BoundedInverseCompact
