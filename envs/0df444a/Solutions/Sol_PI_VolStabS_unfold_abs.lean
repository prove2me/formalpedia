-- Prove2me | solution 1 for PI.VolStabS.unfold_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:51.217841+00:00
-- url     : https://prove2.me/submissions/476f2847-6662-4b40-8a9e-df9e2d7ab802

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LintFibre
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbsAlt
import Theorems.Thm_PI_VolStabS_lint_fibre


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]
namespace PI.VolStabS
theorem _root_.solution {Γ H : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] [μ'.IsInvInvariant]
    (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (ν : Measure Y) (Φ : Y → ℝ≥0∞) (hΦ : AEMeasurable Φ ν)
    (hΨ : Measurable fun g : G => Φ (g • y0))
    (hcov : ν {y | ¬ ∃ g : G, g • y0 = y} = 0)
    (hcomp : ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : Y → G,
      (∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ k, f (s y * (k : G)) ∂μ' ∂ν)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ') :
    ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
  classical

  haveI hcnt : Countable (orbS Γ y0) := by
    have hsub : orbS Γ y0 ⊆ Set.range (fun γ : Γ => (γ : G) • y0) := by
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := hx
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hr : ∀ x : orbS Γ y0, repO Γ y0 x • y0 = (x : Y) := fun x => by
    unfold repO
    exact (Classical.choose_spec x.2).2

  obtain ⟨F0, hF0sub, hF0m, hF0ae⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hc0m : Measurable (cntN Γ F0) := by
    unfold cntN
    exact Measurable.ennreal_tsum fun γ =>
      (measurable_const.indicator hF0m).comp (measurable_const_mul (γ : G))
  have hcfm : Measurable (cfun Γ F0 y0) := by
    unfold cfun
    exact Measurable.ennreal_tsum fun x =>
      (measurable_const.indicator hF0m).comp ((measurable_const_mul _).comp measurable_inv)
  have hc0i : ∀ γ ∈ Γ, ∀ g : G, cntN Γ F0 (γ * g) = cntN Γ F0 g := by
    intro γ hγ g
    unfold cntN
    refine Eq.trans ?_ ((Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
      (fun δ : Γ => F0.indicator (fun _ => (1 : ℝ≥0∞)) ((δ : G) * g)))
    congr 1
    funext δ
    simp [mul_assoc]

  have hsub_ae : ∀ᵐ g ∂μ, ∀ γ : Γ, (γ : G) * g ∈ 𝓕 → (γ : G) * g ∈ F0 := by
    rw [ae_all_iff]
    intro γ
    have h1 : ∀ᵐ x ∂μ, x ∈ 𝓕 → x ∈ F0 := by
      filter_upwards [hF0ae.mem_iff] with x hx h
      exact hx.2 h
    exact (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  have hcov0 : ∀ᵐ g ∂μ, ∃ γ : Γ, (γ : G) * g ∈ F0 := by
    filter_upwards [h𝓕.ae_covers, hsub_ae] with g hg hs
    obtain ⟨γ, hγ⟩ := hg
    exact ⟨γ, hs γ hγ⟩
  have hdis : ∀ᵐ g ∂μ, ∀ γ δ : Γ, γ ≠ δ → ¬ ((γ : G) * g ∈ 𝓕 ∧ (δ : G) * g ∈ 𝓕) := by
    rw [ae_all_iff]
    intro γ
    rw [ae_all_iff]
    intro δ
    by_cases hγδ : γ = δ
    · exact ae_of_all _ fun g h => absurd hγδ h
    · have h0 : μ ((γ⁻¹ • 𝓕) ∩ (δ⁻¹ • 𝓕)) = 0 := h𝓕.aedisjoint (fun h => hγδ (inv_injective h))
      rw [ae_iff]
      refine measure_mono_null ?_ h0
      intro g hg
      simp only [Set.mem_setOf_eq, _root_.not_imp, not_not] at hg
      obtain ⟨-, h1, h2⟩ := hg
      constructor
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact h1
      · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
        exact h2
  have hc01 : ∀ᵐ g ∂μ, cntN Γ F0 g = 1 := by
    filter_upwards [hcov0, hdis] with g hg hd
    obtain ⟨γ, hγ⟩ := hg
    unfold cntN
    rw [tsum_eq_single γ]
    · simp [hγ]
    · intro δ hδ
      have hn : (δ : G) * g ∉ F0 := fun h => hd δ γ hδ ⟨hF0sub h, hF0sub hγ⟩
      simp [hn]
  have hc01i : ∀ᵐ g ∂μ, cntN Γ F0 g⁻¹ = 1 :=
    (Measure.measurePreserving_inv μ).quasiMeasurePreserving.ae hc01
  set Z : Set G := {g | cntN Γ F0 g ≠ 1} with hZ
  have hZm : MeasurableSet Z := hc0m (measurableSet_singleton 1).compl

  let s : Y → G := fun y => if h : ∃ g : G, g • y0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y := fun y h => by
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hsk : ∀ y, (∃ g : G, g • y0 = y) → ∀ k : H, Φ ((s y * (k : G)) • y0) = Φ y := by
    intro y hy k
    rw [mul_smul, (hH k).1 k.2, hs y hy]
  have hsm : ∀ y, Measurable fun k : H => s y * (k : G) :=
    fun y => (measurable_const_mul _).comp measurable_subtype_coe
  have hyae : ∀ᵐ y ∂ν, ∃ g : G, g • y0 = y := ae_iff.2 hcov

  have hmx : ∀ x : orbS Γ y0, Measurable fun h : G => Φ (h⁻¹ • (x : Y)) := by
    intro x
    have e : (fun h : G => Φ (h⁻¹ • (x : Y))) =
        (fun g : G => Φ (g • y0)) ∘ (fun h => h⁻¹ * repO Γ y0 x) := by
      funext h
      simp [Function.comp, mul_smul, hr x]
    rw [e]
    exact hΨ.comp ((measurable_mul_const _).comp measurable_inv)
  have key : ∀ x : orbS Γ y0, ∫⁻ g, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) ∂μ =
      ∫⁻ h in F0, Φ (h⁻¹ • (x : Y)) ∂μ := by
    intro x
    refine (lintegral_inv_eq_self (μ := μ) _).symm.trans ?_
    refine (lintegral_mul_left_eq_self (μ := μ) _ (repO Γ y0 x)⁻¹).symm.trans ?_
    rw [← lintegral_indicator hF0m]
    refine lintegral_congr fun h => ?_
    have e2 : repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹ = h := by group
    have e3 : ((repO Γ y0 x)⁻¹ * h)⁻¹ • y0 = h⁻¹ • (x : Y) := by
      rw [mul_inv_rev, inv_inv, mul_smul, hr x]
    show F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * ((repO Γ y0 x)⁻¹ * h)⁻¹⁻¹) *
      Φ (((repO Γ y0 x)⁻¹ * h)⁻¹ • y0) = _
    rw [e2, e3]
    by_cases hh : h ∈ F0 <;> simp [hh]
  have hL : ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ =
      ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ := by
    rw [setLIntegral_congr hF0ae.symm, lintegral_tsum fun x => (hmx x).aemeasurable]
    have e1 : (fun g => cfun Γ F0 y0 g * Φ (g • y0)) = fun g =>
        ∑' x : orbS Γ y0, F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) := by
      funext g
      unfold cfun
      rw [ENNReal.tsum_mul_right]
    rw [e1, lintegral_tsum (f := fun x g => F0.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
      Φ (g • y0)) fun x => (((measurable_const.indicator hF0m).comp
      ((measurable_const_mul _).comp measurable_inv)).mul hΨ).aemeasurable]
    exact tsum_congr fun x => (key x).symm
  rw [hL]
  apply le_antisymm
  ·
    have hρm : Measurable (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) :=
      measurable_const.indicator hZm.compl
    have hρi : ∀ γ ∈ Γ, ∀ g, (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (γ * g) =
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g := by
      intro γ hγ g
      simp only [Set.indicator, Set.mem_compl_iff, hZ, Set.mem_setOf_eq, hc0i γ hγ g]
    have eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, cfun Γ F0 y0 g *
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hc01i] with g hg
      have hgZ : g⁻¹ ∈ Zᶜ := by simp [hZ, hg]
      rw [Set.indicator_of_mem hgZ, mul_one]
    rw [eq1, hcomp (fun g => cfun Γ F0 y0 g * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹ * Φ (g • y0))
      ((hcfm.mul (hρm.comp measurable_inv)).mul hΨ) s hs,
      ← lintegral_const_mul'' _ hΦ]
    apply lintegral_mono_ae
    filter_upwards [hyae] with y hy
    have e4 : ∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) * (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ *
        Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) *
        (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y := by
      have hm1 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) *
          (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
        (hcfm.comp (hsm y)).mul ((hρm.comp measurable_inv).comp (hsm y))
      rw [← lintegral_mul_const _ hm1]
      exact lintegral_congr fun k => by rw [hsk y hy k]
    rw [e4, lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' _ hρm hρi (s y)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) *
          (Zᶜ.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ'
        ≤ ∫⁻ k in 𝓕', 1 ∂μ' := by
          refine lintegral_mono fun k => ?_
          by_cases hk : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1
          · have hm : (k : G) * (s y)⁻¹ ∈ Zᶜ := by simp [hZ, hk]
            rw [Set.indicator_of_mem hm, hk, mul_one]
          · have hm : (k : G) * (s y)⁻¹ ∉ Zᶜ := by simp [hZ, hk]
            rw [Set.indicator_of_notMem hm, mul_zero]
            exact zero_le_one
      _ = μ' 𝓕' := by rw [setLIntegral_one]
  ·
    have hιm : Measurable (Z.indicator fun _ : G => (1 : ℝ≥0∞)) := measurable_const.indicator hZm
    have eq1 : ∫⁻ g, cfun Γ F0 y0 g * Φ (g • y0) ∂μ = ∫⁻ g, (cfun Γ F0 y0 g +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hc01i] with g hg
      have hgZ : g⁻¹ ∉ Z := by simp [hZ, hg]
      rw [Set.indicator_of_notMem hgZ, mul_zero, add_zero]
    have hfm : Measurable fun g => (cfun Γ F0 y0 g + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) g⁻¹) * Φ (g • y0) :=
      (hcfm.add (measurable_const.mul (hιm.comp measurable_inv))).mul hΨ
    rw [eq1, hcomp _ hfm s hs, ← lintegral_const_mul'' _ hΦ]
    apply lintegral_mono_ae
    filter_upwards [hyae] with y hy
    have hinm : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
      (hcfm.comp (hsm y)).add (measurable_const.mul ((hιm.comp measurable_inv).comp (hsm y)))
    have e4 : ∫⁻ k, (cfun Γ F0 y0 (s y * (k : G)) + ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹) *
        Φ ((s y * (k : G)) • y0) ∂μ' = (∫⁻ k, cfun Γ F0 y0 (s y * (k : G)) +
        ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ') * Φ y := by
      rw [← lintegral_mul_const _ hinm]
      exact lintegral_congr fun k => by rw [hsk y hy k]
    rw [e4]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hfib := lint_fibre μ' y0 hH hF0m 𝓕' h𝓕' (fun _ => (1 : ℝ≥0∞)) measurable_const
      (fun _ _ _ => rfl) (s y)
    simp only [mul_one] at hfib
    have hinv : ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ ∂μ' =
        ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
      refine Eq.trans ?_ (lintegral_inv_eq_self (μ := μ')
        (fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹)))
      refine lintegral_congr fun k => ?_
      simp [mul_inv_rev]
    have hbm : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) :=
      hιm.comp ((measurable_mul_const _).comp measurable_subtype_coe)
    have hm2 : Measurable fun k : H => cfun Γ F0 y0 (s y * (k : G)) := hcfm.comp (hsm y)
    have hm3 : Measurable fun k : H => (Z.indicator fun _ : G => (1 : ℝ≥0∞)) (s y * (k : G))⁻¹ :=
      (hιm.comp measurable_inv).comp (hsm y)
    have hm4 : Measurable fun k : H => cntN Γ F0 ((k : G) * (s y)⁻¹) :=
      hc0m.comp ((measurable_mul_const _).comp measurable_subtype_coe)
    rw [lintegral_add_left hm2, hfib, lintegral_const_mul _ hm3, hinv]
    calc μ' 𝓕' = ∫⁻ k in 𝓕', 1 ∂μ' := by rw [setLIntegral_one]
      _ ≤ ∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) +
          ∞ * (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          refine lintegral_mono fun k => ?_
          by_cases hk : (k : G) * (s y)⁻¹ ∈ Z
          · rw [Set.indicator_of_mem hk]
            simp
          · rw [Set.indicator_of_notMem hk, mul_zero, add_zero]
            have : cntN Γ F0 ((k : G) * (s y)⁻¹) = 1 := by simpa [hZ] using hk
            rw [this]
      _ = (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') +
          ∞ * ∫⁻ k in 𝓕', (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          rw [lintegral_add_left hm4, lintegral_const_mul _ hbm]
      _ ≤ (∫⁻ k in 𝓕', cntN Γ F0 ((k : G) * (s y)⁻¹) ∂μ') +
          ∞ * ∫⁻ k, (Z.indicator fun _ : G => (1 : ℝ≥0∞)) ((k : G) * (s y)⁻¹) ∂μ' := by
          gcongr
          first
          | exact Measure.restrict_le_self
          | exact setLIntegral_le_lintegral _ _
          | exact le_rfl
end PI.VolStabS
