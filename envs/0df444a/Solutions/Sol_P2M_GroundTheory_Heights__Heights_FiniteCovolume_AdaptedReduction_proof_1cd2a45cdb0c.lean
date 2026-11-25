-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_AdaptedReduction_proof_1cd2a45cdb0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:56:26.729682+00:00
-- url     : https://prove2.me/submissions/2ae4888f-1522-44d1-97ef-cfcc489b3ff6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_lineCoeffs_inv_smul_46e4714a8745
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isDIntegral_inv_smul_2409b0090b71
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
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace AdaptedReduction
theorem _root_.solution (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : HyperbolicPairTransitive.Statement h) (h₂ : LineNormalForm.Statement h)
    (h₃ : ComplementLattice.Statement h) : AdaptedReduction.Statement h := by
  intro v₀ w₀ hp h' hh' D
  obtain ⟨KK, hKK, n, hn, H⟩ := h₂ D
  obtain ⟨D', hD'⟩ := h₃ v₀ w₀ hp h' hh' D n hn
  refine ⟨KK, hKK, n, D', hn, fun La l hLa hl => ?_⟩
  obtain ⟨v, w, hvl, hvw, hK, hdec⟩ := H La l hLa hl
  obtain ⟨g, hgv, hgw⟩ := h₁ v₀ w₀ v w hp hvw
  have hI : lineCoeffs (E := E) (g⁻¹ • La) v₀ = lineCoeffs (E := E) La v := by
    rw [lineCoeffs_inv_smul, hgv]
  have hJ : lineCoeffs (E := E) (g⁻¹ • La) w₀ = lineCoeffs (E := E) La w := by
    rw [lineCoeffs_inv_smul, hgw]
  have hwv : h.toSesq w v = 1 := by
    rw [← h.isSymm.eq v w, hvw.2.2, map_one]
  have hsplit : ∀ x ∈ g⁻¹ • La, ∃ a ∈ lineCoeffs (E := E) (g⁻¹ • La) v₀,
      ∃ b ∈ lineCoeffs (E := E) (g⁻¹ • La) w₀,
        n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀ := by
    intro x hx
    rw [mem_inv_smul_iff] at hx
    obtain ⟨ha, hb⟩ := hdec _ hx
    refine ⟨(n : E) * h.toSesq w (g • x), by rw [hI]; exact ha,
      (n : E) * h.toSesq v (g • x), by rw [hJ]; exact hb, ?_⟩
    rw [mem_hypComplement, ← sesq_unitary_smul g v₀, ← sesq_unitary_smul g w₀, hgv, hgw,
      ← Nat.cast_smul_eq_nsmul E, smul_sub, smul_sub, unitary_smul_scalar_smul, unitary_smul_scalar_smul,
      unitary_smul_scalar_smul, hgv, hgw]
    simp only [map_sub, map_smul, smul_eq_mul, hvw.1, hvw.2.1, hvw.2.2, hwv]
    constructor <;> ring
  refine ⟨g, g⁻¹ • La, smul_inv_smul g La, hgv ▸ hvl, ?_, hsplit,
    hD' _ (isDIntegral_inv_smul g hLa) hsplit⟩
  rw [hI, hJ]
  exact hK
end AdaptedReduction
end GroundTheory.Heights₂.Heights.FiniteCovolume
