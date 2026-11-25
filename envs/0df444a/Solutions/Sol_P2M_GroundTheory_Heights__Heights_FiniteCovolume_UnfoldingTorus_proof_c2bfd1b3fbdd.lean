-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldingTorus_proof_c2bfd1b3fbdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:26.903486+00:00
-- url     : https://prove2.me/submissions/4ba6f6c0-b9ec-4402-b7cc-485c7636abaa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldingTorus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHaarParabolicCoordinates
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldingTorus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_mul_76e777226916
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_invApply_of_mem_vecFixGroup_0d425fc8bfb2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_len_invApply_of_mem_stab_df8b20b14c39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecStabGroup_le_vecFixGroup_03fa43eba001
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ae_forall_ne_zero_ea0d0b1a435f
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArchLatticeDiscrete_proof_fb679be34432
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997
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
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace UnfoldingTorus
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (h₂ : HaarParabolicCoordinates.Statement h v) (h₃ : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingTorus.Statement h v := by
  intro M μ _ D La x₀ hLa hx₀ hne hiso
  obtain ⟨ν, κ, τ, hν, -, hκ, hτm, hτ, hμ⟩ := h₂ M μ x₀ hne hiso
  obtain ⟨FD₀, hFD₀, h0, htop⟩ := h₃ D La x₀ hLa hx₀ hne hiso ν hν
  refine ⟨ν FD₀, h0, htop, fun FD hFD t ht => ?_⟩
  set y₀ := vecAt v x₀ with hy₀
  set wt : (InfinitePlace E → ℂ) → ℝ≥0∞ := fun b => ∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))
    with hwt
  set S := {g : archUnitary h v | M.len (invApply g y₀) < t} with hS_def
  set T := {b : InfinitePlace E → ℂ | M.len (fun w => b w • y₀ w) < t} with hT_def
  have hS : MeasurableSet S := measurableSet_below M y₀ t

  have : SecondCountableTopology (vecStabGroup h v La x₀) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : DiscreteTopology (vecStabGroup h v La x₀) := by
    have := ArchLatticeDiscrete.proof h v La hLa.isLattice
    have hle : vecStabGroup h v La x₀ ≤ archLatticeGroup h v La := by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨(γ : h.unitaryGroup), γ.2, rfl⟩
    exact DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective hle)
  have : Countable (vecStabGroup h v La x₀) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let s : (InfinitePlace E → ℂ) × M.stab → archUnitary h v := fun y => τ y.1 * y.2
  have hwtm : Measurable wt :=
    Finset.measurable_prod _ fun w _ => (measurable_pi_apply w).enorm.pow_const _
  have hsm' : Measurable s := (hτm.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  have hsm : Measurable fun p : vecFixGroup h v x₀ × ((InfinitePlace E → ℂ) × M.stab) =>
      (p.1 : archUnitary h v) * s p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul (hsm'.comp measurable_snd)
  have hform : ∀ f : archUnitary h v → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ =
      ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂((volume.withDensity wt).prod κ) := by
    intro f hf
    have hin : Measurable fun y => ∫⁻ x : vecFixGroup h v x₀, f (x * s y) ∂ν :=
      (hf.comp hsm).lintegral_prod_left'
    rw [hμ f hf, lintegral_prod _ hin.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hwtm hin.lintegral_prod_right']
    rfl

  have hf : Measurable (S.indicator (1 : archUnitary h v → ℝ≥0∞)) := measurable_one.indicator hS
  have hinv : ∀ x : vecFixGroup h v x₀, ∀ g,
      S.indicator (1 : archUnitary h v → ℝ≥0∞) (x * g) = S.indicator 1 g := by
    intro x g
    have hx : invApply (x : archUnitary h v) y₀ = y₀ := invApply_of_mem_vecFixGroup x.2
    simp only [hS_def, Set.indicator_apply, Set.mem_ofPred_eq, invApply_mul, hx, Pi.one_apply]
  have key := h₁ M μ (vecFixGroup h v x₀) ν ((volume.withDensity wt).prod κ) s hsm hform
    (vecStabGroup h v La x₀) (vecStabGroup_le_vecFixGroup h v La x₀) FD FD₀ hFD hFD₀ _ hf hinv
  rw [Set.inter_comm, ← Measure.restrict_apply hS, ← lintegral_indicator_one hS, key]
  congr 1

  have hmS : Measurable fun y => S.indicator (1 : archUnitary h v → ℝ≥0∞) (s y) := hf.comp hsm'
  rw [lintegral_prod _ hmS.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hwtm hmS.lintegral_prod_right']
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_ne_zero (InfinitePlace E)] with b hb
  have hk : ∀ k : M.stab, S.indicator (1 : archUnitary h v → ℝ≥0∞) (s (b, k)) =
      T.indicator 1 b := by
    intro k
    simp only [s, Set.indicator_apply, hS_def, hT_def, Set.mem_ofPred_eq, invApply_mul, hτ b hb,
      len_invApply_of_mem_stab M k.2, Pi.one_apply]
  simp only [Pi.mul_apply, hk, lintegral_const, measure_univ, mul_one]
  by_cases hbT : b ∈ T
  · simp [Set.indicator_of_mem hbT]
  · simp [Set.indicator_of_notMem hbT]
end UnfoldingTorus
end GroundTheory.Heights₂.Heights.FiniteCovolume
