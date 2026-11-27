-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnfoldAlongSubgroup_proof_8811d6ae2d7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:06:32.720946+00:00
-- url     : https://prove2.me/submissions/294254e9-5da9-4c75-a985-4d9459e605de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnfoldAlongSubgroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnfoldAlongSubgroup
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
open MeasureTheory
open scoped ENNReal Pointwise
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace UnfoldAlongSubgroup
theorem _root_.solution (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    UnfoldAlongSubgroup.Statement G Y := by
  intro μ H _ ν _ _ ρ _ s hm hμ Γ _ hΓH FD FD₀ hFD hFD₀ f hf hfH
  have hms : ∀ y, Measurable (fun x : H => (x : G) * s y) := fun y =>
    hm.comp measurable_prodMk_right

  have hnull : ∀ Z : Set G, μ Z = 0 →
      ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' Z) = 0 := by
    intro Z hZ
    have hZm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hin : ∀ y, ∫⁻ x, (toMeasurable μ Z).indicator 1 ((x : G) * s y) ∂ν =
        ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := fun y => by
      rw [← lintegral_indicator_one (hZm.preimage (hms y))]
      rfl
    have h0 := hμ ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZm)
    rw [lintegral_indicator_one hZm, measure_toMeasurable, hZ] at h0
    simp only [hin] at h0
    have hmeas : Measurable fun y => ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := by
      simp only [← hin]
      exact ((measurable_one.indicator hZm).comp hm).lintegral_prod_left'
    filter_upwards [(lintegral_eq_zero_iff hmeas).1 h0.symm] with y hy
    exact measure_mono_null (Set.preimage_mono (subset_toMeasurable μ Z)) hy

  let toΓ : Γ.subgroupOf H → Γ := fun γ => ⟨((γ : H) : G), Subgroup.mem_subgroupOf.1 γ.2⟩
  have htoΓ : Function.Injective toΓ := fun a b h => by
    simp only [toΓ, Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have : Countable (Γ.subgroupOf H) := htoΓ.countable

  have hslice : ∀ y (γ : Γ.subgroupOf H) (A : Set G),
      (fun x : H => (x : G) * s y) ⁻¹' ((toΓ γ) • A) =
        γ • ((fun x : H => (x : G) * s y) ⁻¹' A) := by
    intro y γ A
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def,
      smul_eq_mul, toΓ, InvMemClass.coe_inv, Subgroup.coe_mul, mul_assoc]

  obtain ⟨t, htFD, htm, htae⟩ := hFD.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hZ1 : μ {g | ¬ ∃ γ : Γ, γ • g ∈ FD} = 0 := ae_iff.1 hFD.ae_covers
  have hZ2 : μ (FD \ t) = 0 := (ae_eq_set.1 htae).2
  have hZ3 : ∀ γ δ : Γ, ∀ᵐ y ∂ρ, γ ≠ δ →
      ν ((fun x : H => (x : G) * s y) ⁻¹' (γ • FD ∩ δ • FD)) = 0 := by
    intro γ δ
    by_cases h : γ = δ
    · exact ae_of_all _ fun _ h' => absurd h h'
    · filter_upwards [hnull _ (hFD.aedisjoint h)] with y hy _ using hy
  have hgood : ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' t) = ν FD₀ := by
    filter_upwards [hnull _ hZ1, hnull _ hZ2, ae_all_iff.2 fun γ => ae_all_iff.2 (hZ3 γ)]
      with y h1 h2 h3
    have hae : (fun x : H => (x : G) * s y) ⁻¹' t =ᵐ[ν] (fun x : H => (x : G) * s y) ⁻¹' FD := by
      refine ae_eq_set.2 ⟨?_, h2⟩
      rw [Set.sdiff_eq_empty.2 (Set.preimage_mono htFD), measure_empty]
    have hFDy : IsFundamentalDomain (Γ.subgroupOf H) ((fun x : H => (x : G) * s y) ⁻¹' FD) ν :=
      { nullMeasurableSet := (htm.preimage (hms y)).nullMeasurableSet.congr hae
        ae_covers := by
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] at hx
          obtain ⟨γ, hγ⟩ := hx
          refine ⟨⟨⟨γ, hΓH γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_⟩
          simpa only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
            mul_assoc] using hγ
        aedisjoint := by
          intro γ δ hγδ
          change ν (γ • _ ∩ δ • _) = 0
          rw [← hslice, ← hslice, ← Set.preimage_inter]
          exact h3 _ _ (htoΓ.ne hγδ) }
    rw [measure_congr hae, hFDy.measure_eq hFD₀]
  have hsm : Measurable s := by
    convert hm.comp ((measurable_const : Measurable fun _ : Y => (1 : H)).prodMk measurable_id) using 1
    ext y
    simp
  calc ∫⁻ g in FD, f g ∂μ = ∫⁻ g in t, f g ∂μ := setLIntegral_congr htae.symm
    _ = ∫⁻ g, t.indicator f g ∂μ := (lintegral_indicator htm _).symm
    _ = ∫⁻ y, ∫⁻ x, t.indicator f ((x : G) * s y) ∂ν ∂ρ := hμ _ (hf.indicator htm)
    _ = ∫⁻ y, f (s y) * ν ((fun x : H => (x : G) * s y) ⁻¹' t) ∂ρ := by
      refine lintegral_congr fun y => ?_
      have he : (fun x : H => t.indicator f ((x : G) * s y)) =
          ((fun x : H => (x : G) * s y) ⁻¹' t).indicator fun _ => f (s y) := by
        ext x
        by_cases hx : (x : G) * s y ∈ t
        · simp [hx, hfH]
        · simp [hx]
      rw [he, lintegral_indicator_const (htm.preimage (hms y))]
    _ = ∫⁻ y, ν FD₀ * f (s y) ∂ρ := lintegral_congr_ae (by
      filter_upwards [hgood] with y hy
      rw [hy, mul_comm])
    _ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ := lintegral_const_mul _ (hf.comp hsm)
end UnfoldAlongSubgroup
end GroundTheory.Heights₂.Heights.FiniteCovolume
