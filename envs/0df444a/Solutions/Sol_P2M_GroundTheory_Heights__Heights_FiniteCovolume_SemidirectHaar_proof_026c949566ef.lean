-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectHaar_proof_026c949566ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:07.347952+00:00
-- url     : https://prove2.me/submissions/b2e1950a-fa92-4a61-b046-7120fc5fcbed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
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
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace SemidirectHaar
theorem _root_.solution (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] :
    SemidirectHaar.Statement G T := by
  intro P H hP hH hHP τ β δ hτ hβ hδc hτP _ hτH hβH μ _ ν _ ρ _ hδ
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))
  have : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))

  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hUo : IsOpen (interior K) := isOpen_interior
  have hU1 : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK1
  set f : G → ℝ≥0∞ := (interior K).indicator 1 with hf_def
  have hfm : Measurable f := measurable_one.indicator hUo.measurableSet
  have hI : ∫⁻ x : H, f x ∂ν = ν (Subtype.val ⁻¹' interior K) := by
    rw [← lintegral_indicator_one (hUo.preimage continuous_subtype_val).measurableSet]
    congr 1
  have hI0 : ∫⁻ x : H, f x ∂ν ≠ 0 := by
    rw [hI]
    exact ((hUo.preimage continuous_subtype_val).measure_pos ν ⟨1, hU1⟩).ne'
  have hItop : ∫⁻ x : H, f x ∂ν ≠ ∞ := by
    rw [hI]
    exact ((measure_mono (Set.preimage_mono interior_subset)).trans_lt
      (hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top).ne

  have hmul : ∀ s t, δ (s * t) = δ s * δ t := by
    intro s t
    have e1 := hδ (s * t) f hfm
    have e2 : ∫⁻ x : H, f (τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹) ∂ν =
        δ t * ∫⁻ x : H, f (τ s * x * (τ s)⁻¹) ∂ν :=
      hδ t (fun z => f (τ s * z * (τ s)⁻¹))
        (hfm.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable)
    have e3 := hδ s f hfm
    have e : ∫⁻ x : H, f (τ (s * t) * x * (τ (s * t))⁻¹) ∂ν =
        ∫⁻ x : H, f (τ s * (τ t * x * (τ t)⁻¹) * (τ s)⁻¹) ∂ν := by
      congr 1
      funext x
      simp only [map_mul, mul_inv_rev, mul_assoc]
    rw [e, e2, e3, ← mul_assoc] at e1
    have h := (ENNReal.mul_left_inj hI0 hItop).1 e1
    exact (ENNReal.coe_injective (by rw [ENNReal.coe_mul]; exact h)).symm.trans (mul_comm _ _)
  have hone : δ 1 = 1 := by
    have e := hδ 1 f hfm
    simp only [map_one, one_mul, inv_one, mul_one] at e
    have h := (ENNReal.mul_left_inj hI0 hItop).1 (e.symm.trans (one_mul _).symm)
    exact_mod_cast h
  have hpos : ∀ t, δ t ≠ 0 := fun t h => by
    have e := hmul t t⁻¹
    rw [mul_inv_cancel, hone, h, zero_mul] at e
    exact one_ne_zero e

  let Φ : T × H → P := fun q => ⟨(q.2 : G) * τ q.1, P.mul_mem (hHP q.2.2) (hτP q.1)⟩
  have hΦc : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hτ.comp continuous_fst)).subtype_mk _
  have hΦm : Measurable Φ := hΦc.measurable
  have hδm : Measurable fun t => (δ t : ℝ≥0∞) := (ENNReal.continuous_coe.comp hδc).measurable
  let m : Measure P := Measure.map Φ ((ρ.withDensity fun t => (δ t : ℝ≥0∞)).prod ν)
  have hm : ∀ ψ : P → ℝ≥0∞, Measurable ψ →
      ∫⁻ p, ψ p ∂m = ∫⁻ t, δ t * ∫⁻ x : H, ψ (Φ (t, x)) ∂ν ∂ρ := by
    intro ψ hψ
    rw [lintegral_map hψ hΦm, lintegral_prod (fun z => ψ (Φ z)) (hψ.comp hΦm).aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hδm]
    · rfl
    · exact (hψ.comp hΦm).lintegral_prod_right'

  have hinv : ∀ (p₀ : P) (ψ : P → ℝ≥0∞), Measurable ψ →
      ∫⁻ p, ψ (p₀ * p) ∂m = ∫⁻ p, ψ p ∂m := by
    intro p₀ ψ hψ
    rw [hm (fun p => ψ (p₀ * p)) (hψ.comp (measurable_const_mul p₀)), hm _ hψ]
    set s := β p₀ with hs
    let y : H := ⟨(p₀ : G) * (τ s)⁻¹, hβH p₀⟩
    let ψ' : G → ℝ≥0∞ := Function.extend Subtype.val ψ 0
    have hψ' : Measurable ψ' :=
      (MeasurableEmbedding.subtype_coe hP.measurableSet).measurable_extend hψ measurable_const
    have hψ'e : ∀ p : P, ψ' p = ψ p := fun p => Subtype.val_injective.extend_apply ψ 0 p
    have inner : ∀ t, ∫⁻ x : H, ψ (p₀ * Φ (t, x)) ∂ν =
        δ s * ∫⁻ x : H, ψ (Φ (s * t, x)) ∂ν := by
      intro t
      have h1 : ∫⁻ x : H, ψ' ((y : G) * (τ s * x * (τ s)⁻¹) * τ (s * t)) ∂ν =
          δ s * ∫⁻ x : H, ψ' ((y : G) * x * τ (s * t)) ∂ν :=
        hδ s (fun z => ψ' ((y : G) * z * τ (s * t)))
          (hψ'.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable)
      have h2 : ∫⁻ x : H, ψ' ((y : G) * x * τ (s * t)) ∂ν = ∫⁻ x : H, ψ (Φ (s * t, x)) ∂ν := by
        rw [← lintegral_mul_left_eq_self (μ := ν) (fun x : H => ψ (Φ (s * t, x))) y]
        congr 1
        funext x
        rw [← hψ'e]
        rfl
      rw [← h2, ← h1]
      congr 1
      funext x
      rw [← hψ'e]
      congr 1
      simp only [Φ, y, Subgroup.coe_mul, map_mul]
      group
    refine Eq.trans ?_ (lintegral_mul_left_eq_self (μ := ρ)
      (fun u => (δ u : ℝ≥0∞) * ∫⁻ x : H, ψ (Φ (u, x)) ∂ν) s)
    congr 1
    funext t
    rw [inner, hmul, ENNReal.coe_mul]
    ring
  have : Measure.IsMulLeftInvariant m := by
    constructor
    intro p₀
    ext S hS
    rw [Measure.map_apply (measurable_const_mul p₀) hS, ← lintegral_indicator_one hS,
      ← lintegral_indicator_one (measurable_const_mul p₀ hS)]
    exact hinv p₀ _ (measurable_one.indicator hS)

  have hβΦ : ∀ t (x : H), β (Φ (t, x)) = t := by
    intro t x
    have h := H.mul_mem (H.inv_mem x.2) (hβH (Φ (t, x)))
    have h' : τ (t * (β (Φ (t, x)))⁻¹) ∈ H := by
      simpa [Φ, map_mul, map_inv, mul_assoc] using h
    exact (mul_inv_eq_one.1 (hτH _ h')).symm
  let α : P → H := fun p => ⟨(p : G) * (τ (β p))⁻¹, hβH p⟩
  have hα : Continuous α :=
    (continuous_subtype_val.mul (hτ.comp hβ).inv).subtype_mk _
  have hαΦ : ∀ t (x : H), α (Φ (t, x)) = x := by
    intro t x
    apply Subtype.ext
    simp only [α, hβΦ]
    simp [Φ]
  have : IsFiniteMeasureOnCompacts m := by
    constructor
    intro K hK
    have hL : IsCompact (closure K) := hK.closure
    refine (measure_mono subset_closure).trans_lt ?_
    have hLm : MeasurableSet (closure K) := isClosed_closure.measurableSet
    obtain ⟨C, hC⟩ := (hL.image hβ).bddAbove_image hδc.continuousOn
    rw [← lintegral_indicator_one hLm, hm _ (measurable_one.indicator hLm)]
    calc ∫⁻ t, δ t * ∫⁻ x : H, (closure K).indicator 1 (Φ (t, x)) ∂ν ∂ρ
        ≤ ∫⁻ t, (β '' closure K).indicator (fun _ => (C : ℝ≥0∞) * ν (α '' closure K)) t ∂ρ := by
          refine lintegral_mono fun t => ?_
          by_cases ht : t ∈ β '' closure K
          · rw [Set.indicator_of_mem ht]
            gcongr
            · exact_mod_cast hC ⟨t, ht, rfl⟩
            · calc ∫⁻ x : H, (closure K).indicator 1 (Φ (t, x)) ∂ν
                  ≤ ∫⁻ x : H, (α '' closure K).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
                    refine lintegral_mono fun x => ?_
                    by_cases hx : Φ (t, x) ∈ closure K
                    · rw [Set.indicator_of_mem hx,
                        Set.indicator_of_mem (show x ∈ α '' closure K from ⟨Φ (t, x), hx, hαΦ t x⟩)]
                      rfl
                    · rw [Set.indicator_of_notMem hx]
                      exact bot_le
                _ ≤ 1 * ν (α '' closure K) := lintegral_indicator_const_le _ _
                _ = ν (α '' closure K) := one_mul _
          · have h0 : ∀ x : H, (closure K).indicator (1 : P → ℝ≥0∞) (Φ (t, x)) = 0 :=
              fun x => Set.indicator_of_notMem (fun hx => ht ⟨Φ (t, x), hx, hβΦ t x⟩) _
            simp [h0]
      _ ≤ (C : ℝ≥0∞) * ν (α '' closure K) * ρ (β '' closure K) :=
          lintegral_indicator_const_le _ _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top
          (hL.image hα).measure_lt_top) (hL.image hβ).measure_lt_top

  have hm0 : m ≠ 0 := by
    intro h0
    have e := hm (fun _ => 1) measurable_const
    rw [h0, lintegral_zero_measure] at e
    simp only [lintegral_const, one_mul] at e
    rw [lintegral_mul_const _ hδm] at e
    have hν : ν Set.univ ≠ 0 := isOpen_univ.measure_ne_zero ν Set.univ_nonempty
    have hρ : ∫⁻ t, (δ t : ℝ≥0∞) ∂ρ ≠ 0 := by
      rw [Ne, lintegral_eq_zero_iff hδm]
      intro h
      have hF : ∀ᵐ _t ∂ρ, False := h.mono fun t ht => hpos t (by simpa using ht)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hF
      exact isOpen_univ.measure_ne_zero ρ Set.univ_nonempty (by rw [hF]; rfl)
    exact mul_ne_zero hρ hν e.symm

  have hsc := Measure.isMulLeftInvariant_eq_smul m μ
  set c₀ := Measure.haarScalarFactor m μ with hc₀
  have hc0 : c₀ ≠ 0 := by
    intro h
    apply hm0
    rw [hsc, h, zero_smul]
  refine ⟨c₀⁻¹, inv_ne_zero hc0, fun φ hφ => ?_⟩
  have key : ∫⁻ p, φ p ∂m = ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ :=
    hm _ (hφ.comp continuous_subtype_val.measurable)
  rw [hsc, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul] at key
  rw [← key, ENNReal.coe_inv hc0, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hc0) ENNReal.coe_ne_top, one_mul]
end SemidirectHaar
end GroundTheory.Heights₂.Heights.FiniteCovolume
