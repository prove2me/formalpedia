-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ArithmeticCovolumeFinite_proof_3bb26052265c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:48:50.649002+00:00
-- url     : https://prove2.me/submissions/5721dbc8-b6a5-4f07-864d-feb1038243a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArithmeticCovolumeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_invApply_3885da6a041b
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_lineIndex_smul_f78a06c73a31
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
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ArithmeticCovolumeFinite
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ScalingLaw.Statement h v) (h₂ : MahlerCompactness.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : ShortestVectorIndex.Statement h v)
    (h₅ : IntegralFamilyBound.Statement E) (h₆ : MajorantExists.Statement h v)
    (h₈ : ArchLatticeDiscrete.Statement h v) (h₉ : LatticePointsBelowFinite.Statement h v) :
    ArithmeticCovolumeFinite.Statement h v := by
  classical
  intro μ _ D La hLa
  obtain ⟨M⟩ := h₆

  obtain ⟨r, a, ha, har⟩ := h₅
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]
  have ha' : ∃ b : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg.symm, ha.comp _ (Fin.cast_injective _), fun i σ => har _ σ⟩
  set C₀ : ℕ := ⌊(r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)⌋₊ with hC₀

  set VV : Set W := {x | x ∈ La ∧ x ≠ 0 ∧ h.toSesq x x = 0 ∧ lineIndex E La x ≤ C₀} with hVV
  have hstable : ∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV := by
    intro γ hγ x hx
    have hγ' : γ • La = La := MulAction.mem_stabilizer_iff.1 hγ
    refine ⟨?_, fun h0 => hx.2.1 ((smul_eq_zero_iff_eq γ).1 h0), ?_, ?_⟩
    · have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul _ _ _ hx.1
      rwa [hγ'] at h1
    · rw [← hx.2.2.1]
      exact HermitianForm.mem_unitaryGroup.1 γ.2 x x
    · rw [GaussianPlane.lineIndex_smul hγ']
      exact hx.2.2.2
  obtain ⟨FD, hFD, hm⟩ := h₁ M μ D La VV hLa (fun x hx => hx.1) (fun x hx => ⟨hx.2.1, hx.2.2.1⟩)
    hstable ⟨C₀, fun x hx => hx.2.2.2⟩
  refine ⟨FD, hFD, ?_⟩

  set B : Set (archUnitary h v) :=
    ⋃ x : W, ⋃ (_ : x ∈ La ∧ x ≠ 0), {g | M.len (invApply g (vecAt v x)) < 1} with hB
  have hBmeas : MeasurableSet B :=
    (isOpen_iUnion fun x => isOpen_iUnion fun _ =>
      isOpen_lt (continuous_len_invApply M _) continuous_const).measurableSet
  have hBle : μ (FD ∩ B) ≤ massBelow M μ FD VV 1 := by
    rw [Set.inter_comm, ← Measure.restrict_apply hBmeas, ← lintegral_indicator_one hBmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨x₁, hx₁⟩ := Set.mem_iUnion.1 hg
      obtain ⟨⟨hx₁La, hx₁0⟩, hx₁lt⟩ := Set.mem_iUnion.1 hx₁
      set S : Set W := {x | x ∈ La ∧ M.len (invApply g (vecAt v x)) < 1} ∩ {x | x ≠ 0}
      have hSfin : S.Finite := (h₉ M La g 1 hLa.isLattice).inter_of_left _
      obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image S (fun x => M.len (invApply g (vecAt v x)))
        hSfin ⟨x₁, ⟨hx₁La, hx₁lt⟩, hx₁0⟩
      obtain ⟨⟨hxLa, hxlt⟩, hx0⟩ := hxS
      have hshort : ∀ y ∈ La, y ≠ 0 →
          M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)) := by
        intro y hy hy0
        by_cases hylt : M.len (invApply g (vecAt v y)) < 1
        · exact hxmin y ⟨⟨hy, hylt⟩, hy0⟩
        · exact hxlt.le.trans (not_lt.1 hylt)
      have hxVV : x ∈ VV := by
        refine ⟨hxLa, hx0, h₃ M D La g x hLa hxLa hxlt, ?_⟩
        exact Nat.le_floor (h₄ M r ha' D La g x hLa hxLa hx0 hshort)
      have hne : ({y ∈ VV | M.len (invApply g (vecAt v y)) < 1}).Nonempty := ⟨x, hxVV, hxlt⟩
      unfold countBelow
      rw [← ENat.toENNReal_one, ENat.toENNReal_le]
      exact Set.one_le_encard_iff_nonempty.2 hne
    · rw [Set.indicator_of_notMem hg]
      exact bot_le

  obtain ⟨S, hS, K, hK, hMah⟩ := h₂ M D 1 one_pos
  have : DiscreteTopology (archLatticeGroup h v La) := h₈ La hLa.isLattice
  have : Countable (archLatticeGroup h v La) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let c : AddSubgroup W → h.unitaryGroup := fun L =>
    if hL : ∃ γ : h.unitaryGroup, γ • La = L then hL.choose else 1
  set K' : Set (archUnitary h v) :=
    ⋃ L ∈ S, (fun k => (archEmbed h v (c L))⁻¹ * k) '' K with hK'
  have hK'c : IsCompact K' :=
    hS.isCompact_biUnion fun L _ => hK.image (continuous_const.mul continuous_id)
  have hcover : FD ∩ Bᶜ ⊆ ⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD := by
    rintro g ⟨hgFD, hgB⟩
    have hlam : ∀ x ∈ La, x ≠ 0 → (1 : ℝ) ≤ M.len (invApply g (vecAt v x)) := by
      intro x hx hx0
      by_contra hlt
      exact hgB (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨⟨hx, hx0⟩, not_le.1 hlt⟩⟩)
    obtain ⟨γ, hγS, hγK⟩ := hMah La g hLa hlam
    have hL : ∃ γ' : h.unitaryGroup, γ' • La = γ • La := ⟨γ, rfl⟩
    have hcL : c (γ • La) • La = γ • La := by
      simp only [c, dif_pos hL]
      exact hL.choose_spec
    have hstab : γ⁻¹ * c (γ • La) ∈ latticeStab h La := by
      change (γ⁻¹ * c (γ • La)) • La = La
      rw [mul_smul, hcL, inv_smul_smul]
    refine Set.mem_iUnion.2 ⟨⟨archEmbed h v (γ⁻¹ * c (γ • La)), Subgroup.mem_map_of_mem _ hstab⟩,
      ?_, hgFD⟩
    refine Set.mem_smul_set.2 ⟨(archEmbed h v (c (γ • La)))⁻¹ * (archEmbed h v γ * g),
      Set.mem_biUnion hγS ⟨_, hγK, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [map_mul, map_inv]
    group
  have hAlt : μ (FD ∩ Bᶜ) < ⊤ := by
    calc μ (FD ∩ Bᶜ) ≤ μ (⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD) := measure_mono hcover
      _ ≤ ∑' δ : archLatticeGroup h v La, μ (δ • K' ∩ FD) := measure_iUnion_le _
      _ = μ K' := (hFD.measure_eq_tsum K').symm
      _ < ⊤ := hK'c.measure_lt_top
  calc μ FD = μ ((FD ∩ B) ∪ (FD ∩ Bᶜ)) := by rw [Set.inter_union_compl]
    _ ≤ μ (FD ∩ B) + μ (FD ∩ Bᶜ) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hBle.trans_lt (hm 1 one_pos).1, hAlt⟩
end ArithmeticCovolumeFinite
end GroundTheory.Heights₂.Heights.FiniteCovolume
