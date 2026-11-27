-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_HaarParabolicCoordinates_proof_c5f720c5feb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:55:58.792853+00:00
-- url     : https://prove2.me/submissions/bc78e7af-9829-480b-a2ec-5eee37d7726f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsArchUnimodular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsMajorantStabCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHaarParabolicCoordinates
import Theorems.Thm_GroundTheory_Automorphic_HaarSK_exists_lintegral_eq
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
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace HaarParabolicCoordinates
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ParabolicDecomposition.Statement h v) (h₂ : ArchUnimodular.Statement h v)
    (h₃ : MajorantStabCompact.Statement h v) (h₄ : LineStabHaar.Statement h v) :
    HaarParabolicCoordinates.Statement h v := by
  intro M μ _ x₀ hx₀ hiso
  have : μ.IsMulRightInvariant := h₂ μ
  have : CompactSpace M.stab := isCompact_iff_compactSpace.mp (h₃ M)
  set κ : Measure M.stab := Measure.haarMeasure ⊤ with hκ
  have : IsProbabilityMeasure κ :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts M.stab))⟩
  have hSK : Function.Surjective (HaarSK.mulMap (lineStab h v x₀) M.stab) := by
    intro g
    obtain ⟨p, k, hk, rfl, hp⟩ := h₁ M x₀ hx₀ hiso g
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c, -, hc⟩ := HaarSK.exists_lintegral_eq μ (isClosed_lineStab h v x₀) (h₃ M) hSK
    (Measure.haar : Measure (lineStab h v x₀)) κ
  obtain ⟨ν, τ, hν, hτ, -, hτx, hP⟩ := h₄ x₀ hx₀ hiso Measure.haar
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h1 := hc 1 measurable_const
    rw [h0, zero_mul] at h1
    simp only [Pi.one_apply, lintegral_const, one_mul] at h1
    exact (Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h1
  have := hν
  refine ⟨(c : ℝ≥0∞) • ν, κ, τ, Measure.IsHaarMeasure.smul ν hc0 ENNReal.coe_ne_top, inferInstance,
    inferInstance, hτ, hτx, fun f hf => ?_⟩
  have hφ : Measurable fun g : archUnitary h v => ∫⁻ k : M.stab, f (g * k) ∂κ :=
    (hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'
  have hPφ := hP _ hφ
  rw [hc f hf, hPφ, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun b => ?_
  have hswap : ∫⁻ x : vecFixGroup h v x₀, ∫⁻ k : M.stab, f ((x : archUnitary h v) * τ b * k) ∂κ ∂ν =
      ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f ((x : archUnitary h v) * (τ b * k)) ∂ν ∂κ := by
    rw [lintegral_lintegral_swap]
    · simp only [mul_assoc]
    · exact (hf.comp (((measurable_subtype_coe.comp measurable_fst).mul_const (τ b)).mul
        (measurable_subtype_coe.comp measurable_snd))).aemeasurable
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, hswap]
  ring
end HaarParabolicCoordinates
end GroundTheory.Heights₂.Heights.FiniteCovolume
