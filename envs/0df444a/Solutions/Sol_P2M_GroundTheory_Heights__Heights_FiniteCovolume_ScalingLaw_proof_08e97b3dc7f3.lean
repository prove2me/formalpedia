-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ScalingLaw_proof_08e97b3dc7f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:03.215799+00:00
-- url     : https://prove2.me/submissions/db0bd201-33e1-428e-98c4-16123d3b1efd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_tsum_orbit_eq_tsum_quotient_4af71a9ca89b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_belowIndicator_b4d0ba7dc339
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_smul_vecAt_b12bc12835a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_stabilizer_vecAt_ade5addf10ad
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective
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
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
attribute [local instance] archMulAction
variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ScalingLaw
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : UnfoldingIntegral.Statement h v) (h₂ : VectorOrbitsFinite.Statement h)
    (h₃ : UnfoldOrbit.Statement (archUnitary h v))
    (h₄ : DiscreteFundamentalDomain.Statement (archUnitary h v))
    (h₅ : ArchLatticeDiscrete.Statement h v) : ScalingLaw.Statement h v := by
  classical
  intro M μ _ D La VV hLa hVV hiso hstab hC
  set Γ := archLatticeGroup h v La with hΓ
  have : DiscreteTopology Γ := h₅ La hLa.isLattice
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hQc : ∀ K : Subgroup Γ, Countable (Γ ⧸ K) := fun K => QuotientGroup.mk_surjective.countable
  obtain ⟨FD, -, hFD⟩ := h₄ μ Γ inferInstance

  have key : ∀ y ∈ VV, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t : ℝ, 0 < t →
      ∫⁻ g in FD, ∑' q : Γ ⧸ (vecStabGroup h v La y).subgroupOf Γ,
        belowIndicator M (vecAt v y) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) ∂μ =
        C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro y hy
    obtain ⟨FD₀, hFD₀, C, -, hCtop, hCt⟩ :=
      h₁ M μ D La y hLa (hVV hy) (hiso y hy).1 (hiso y hy).2
    refine ⟨C, hCtop, fun t ht => ?_⟩
    have hle : vecStabGroup h v La y ≤ Γ := by
      rintro _ ⟨ε, -, rfl⟩
      exact Subgroup.mem_map.2 ⟨ε.1, ε.2, rfl⟩
    have hinv : ∀ γ ∈ vecStabGroup h v La y, ∀ g,
        belowIndicator M (vecAt v y) t (γ * g) = belowIndicator M (vecAt v y) t g := by
      intro γ hγ g
      obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.1 hγ
      have hb : ((archEmbed h v).comp (latticeStab h La).subtype ε) • vecAt v y = vecAt v y := by
        change archEmbed h v (ε : h.unitaryGroup) • vecAt v y = vecAt v y
        rw [archEmbed_smul_vecAt]
        exact congrArg (vecAt v) (MulAction.mem_stabilizer_iff.1 hε)
      have hb' := (inv_smul_eq_iff.2 hb.symm).symm
      simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, mul_smul,
        ← hb', Pi.one_apply]
    rw [h₃ μ Γ _ hle FD FD₀ hFD hFD₀ _ (measurable_belowIndicator M (vecAt v y) t) hinv,
      belowIndicator, lintegral_indicator_one (measurableSet_below M _ t),
      Measure.restrict_apply (measurableSet_below M _ t), Set.inter_comm]
    exact hCt t ht
  choose! Cf hCf hCeq using key

  obtain ⟨S, hSV, hScov⟩ := h₂ D La VV hLa hVV hiso hstab hC
  let T : Finset (Set (InfinitePlace E → ι → ℂ)) :=
    S.image fun y => MulAction.orbit Γ (vecAt v y)
  have hT : ∀ o ∈ T, ∃ y, y ∈ S ∧ MulAction.orbit Γ (vecAt v y) = o := fun o ho => by
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 ho
    exact ⟨y, hy, e⟩
  choose! Y hYS hYo using hT
  have hP : vecAt v '' VV = ⋃ o ∈ (T : Set (Set (InfinitePlace E → ι → ℂ))), o := by
    ext p
    simp only [Set.mem_iUnion, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hyS, γ, hγ, rfl⟩ := hScov x hx
      refine ⟨MulAction.orbit Γ (vecAt v y), Finset.mem_image.2 ⟨y, hyS, rfl⟩, ?_⟩
      rw [← archEmbed_smul_vecAt]
      exact ⟨⟨archEmbed h v γ, Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩⟩, rfl⟩
    · rintro ⟨o, ho, hp⟩
      rw [← hYo o ho] at hp
      obtain ⟨⟨γ', hγ'⟩, rfl⟩ := hp
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hγ'
      exact ⟨γ • Y o, hstab γ hγ _ (hSV (hYS o ho)), (archEmbed_smul_vecAt h v γ (Y o)).symm⟩
  have hdisj : (T : Set (Set (InfinitePlace E → ι → ℂ))).PairwiseDisjoint fun o => o := by
    intro o₁ h₁' o₂ h₂' hne
    refine Set.disjoint_left.2 fun p hp1 hp2 => hne ?_
    rw [← hYo o₁ h₁'] at hp1 ⊢
    rw [← hYo o₂ h₂'] at hp2 ⊢
    exact (MulAction.orbit_eq_iff.2 hp1).symm.trans (MulAction.orbit_eq_iff.2 hp2)

  have hcount : ∀ g t, countBelow M VV g t = ∑ o ∈ T,
      ∑' q : Γ ⧸ (vecStabGroup h v La (Y o)).subgroupOf Γ,
        belowIndicator M (vecAt v (Y o)) t (((Quotient.out q : Γ) : archUnitary h v)⁻¹ * g) := by
    intro g t
    have hPA : vecAt v '' {x ∈ VV | M.len (invApply g (vecAt v x)) < t} =
        vecAt v '' VV ∩ {p | M.len (g⁻¹ • p) < t} := by
      ext p
      constructor
      · rintro ⟨x, ⟨hx, hxt⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, hxt⟩
      · rintro ⟨⟨x, hx, rfl⟩, hxt⟩
        exact ⟨x, ⟨hx, hxt⟩, rfl⟩
    have h1 : countBelow M VV g t =
        ∑' p : (vecAt v '' VV : Set _), {p | M.len (g⁻¹ • p) < t}.indicator 1 (p : _) := by
      rw [countBelow, ← (vecAt_injective v).encard_image, hPA, ← ENNReal.tsum_set_one,
        tsum_subtype (vecAt v '' VV), Set.indicator_indicator, ← tsum_subtype]
      rfl
    rw [h1, hP, ENNReal.tsum_biUnion' hdisj]
    refine (Finset.tsum_subtype' T fun o : Set (InfinitePlace E → ι → ℂ) =>
      ∑' p : o, {p | M.len (g⁻¹ • p) < t}.indicator (1 : (InfinitePlace E → ι → ℂ) → ℝ≥0∞) (p : InfinitePlace E → ι → ℂ)).trans ?_
    refine Finset.sum_congr rfl fun o ho => ?_
    rw [tsum_orbit_eq_tsum_quotient (vecAt v (Y o)) o (hYo o ho) _ (stabilizer_vecAt h v La (Y o))]
    refine tsum_congr fun q => ?_
    simp only [belowIndicator, Set.indicator_apply, Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv,
      mul_smul]
    rfl
  have hm : ∀ t : ℝ, 0 < t → massBelow M μ FD VV t =
      ∑ o ∈ T, Cf (Y o) * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1))) := by
    intro t ht
    rw [massBelow, lintegral_congr fun g => hcount g t, lintegral_finset_sum]
    · exact Finset.sum_congr rfl fun o ho => hCeq (Y o) (hSV (hYS o ho)) t ht
    · exact fun o _ => @Measurable.ennreal_tsum _ _ _ (hQc _) _ fun q =>
        (measurable_belowIndicator M _ t).comp (measurable_const_mul _)
  refine ⟨FD, hFD, fun t ht => ⟨?_, fun θ hθ => ?_⟩⟩
  · rw [hm t ht]
    exact ENNReal.sum_lt_top.2 fun o ho =>
      ENNReal.mul_lt_top (hCf _ (hSV (hYS o ho))) ENNReal.ofReal_lt_top
  · rw [hm (θ * t) (mul_pos hθ ht), hm t ht, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hθ.le _)]
    ring
end ScalingLaw
end GroundTheory.Heights₂.Heights.FiniteCovolume
