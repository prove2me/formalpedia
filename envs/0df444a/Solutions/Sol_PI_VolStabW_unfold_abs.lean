-- Prove2me | solution 1 for PI.VolStabW.unfold_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:59.563496+00:00
-- url     : https://prove2.me/submissions/a633658f-46da-48f5-9f75-22cd0c09ea13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LintFibre
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbsAlt
import Theorems.Thm_PI_VolStabW_cntN_mul
import Theorems.Thm_PI_VolStabW_fd_count_ae
import Theorems.Thm_PI_VolStabW_fd_of_subset
import Theorems.Thm_PI_VolStabW_lint_fibre
import Theorems.Thm_PI_VolStabW_lint_mul_right
import Theorems.Thm_PI_VolStabW_meas_cfun
import Theorems.Thm_PI_VolStabW_meas_cntN
import Theorems.Thm_PI_VolStabW_repO_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]
namespace PI.VolStabW
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
  have hsub : orbS Γ y0 ⊆ Set.range (fun γ : Γ => (γ : G) • y0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  have hcO : Countable (orbS Γ y0) :=
    ((Set.countable_range fun γ : Γ => (γ : G) • y0).mono hsub).to_subtype
  obtain ⟨A, hA𝓕, hAm, hAe⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hA : IsFundamentalDomain Γ A μ := fd_of_subset h𝓕 hA𝓕 hAm (ae_eq_set.1 hAe).2
  have hNm : Measurable (cntN Γ A) := meas_cntN Γ hAm
  have hcm : Measurable (cfun Γ A y0) := meas_cfun Γ y0 hAm
  have hN1 : ∀ᵐ g ∂μ, cntN Γ A g⁻¹ = 1 := by
    have h0 : μ {g | cntN Γ A g ≠ 1} = 0 := measure_eq_zero_iff_ae_notMem.2 (by
      filter_upwards [fd_count_ae hA] with g hg
      exact fun h => h hg)
    have h0' : μ (Inv.inv ⁻¹' {g | cntN Γ A g ≠ 1}) = 0 := by
      rw [Measure.measure_preimage_inv]; exact h0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0'] with g hg
    by_contra h
    exact hg h

  have step1 : ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ =
      ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ := by
    rw [setLIntegral_congr hAe.symm, ← lintegral_indicator hAm, ← lintegral_inv_eq_self]
    have hpt : ∀ g : G, A.indicator (fun h => ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y))) g⁻¹ =
        ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) g⁻¹ *
          Φ ((g * repO Γ y0 x) • y0) := by
      intro g
      by_cases hg : g⁻¹ ∈ A
      · simp only [indicator_of_mem hg, one_mul, inv_inv]
        refine tsum_congr fun x => ?_
        rw [mul_smul, repO_smul]
      · simp only [indicator_of_notMem hg, zero_mul, tsum_zero]
    have hmx : ∀ x : orbS Γ y0, Measurable fun g : G =>
        A.indicator (fun _ => (1 : ℝ≥0∞)) g⁻¹ * Φ ((g * repO Γ y0 x) • y0) := fun x =>
      ((measurable_const.indicator hAm).comp measurable_inv).mul
        (hΨ.comp (measurable_mul_const _))
    have hmx' : ∀ x : orbS Γ y0, Measurable fun g : G =>
        A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) := fun x =>
      ((measurable_const.indicator hAm).comp ((measurable_const_mul _).comp measurable_inv)).mul hΨ
    calc ∫⁻ g, A.indicator (fun h => ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y))) g⁻¹ ∂μ
        = ∑' x : orbS Γ y0, ∫⁻ g, A.indicator (fun _ => (1 : ℝ≥0∞)) g⁻¹ *
            Φ ((g * repO Γ y0 x) • y0) ∂μ := by
          rw [lintegral_congr hpt, lintegral_tsum fun x => (hmx x).aemeasurable]
      _ = ∑' x : orbS Γ y0, ∫⁻ g, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
            Φ (g • y0) ∂μ := by
          refine tsum_congr fun x => ?_
          rw [← lint_mul_right (μ := μ) (fun g => A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * g⁻¹) * Φ (g • y0)) (repO Γ y0 x)]
          refine lintegral_congr fun g => ?_
          simp only [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = ∫⁻ g, ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
            Φ (g • y0) ∂μ := (lintegral_tsum fun x => (hmx' x).aemeasurable).symm
      _ = ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ := by
          refine lintegral_congr fun g => ?_
          rw [ENNReal.tsum_mul_right, mul_comm]
          rfl

  let s : Y → G := fun y => if h : ∃ g : G, g • y0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y := fun y h => by
    simp only [s, dif_pos h]; exact h.choose_spec
  have hΨs : ∀ y, (∃ g : G, g • y0 = y) → ∀ k : H, Φ ((s y * (k : G)) • y0) = Φ y :=
    fun y h k => by rw [mul_smul, (hH _).1 k.2, hs y h]
  have hOrb : ∀ᵐ y ∂ν, ∃ g : G, g • y0 = y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov] with y hy
    by_contra h
    exact hy h
  have hmk : ∀ s0 : G, Measurable fun k : H => s0 * (k : G) :=
    fun s0 => (measurable_const_mul s0).comp measurable_subtype_coe

  let ρ1 : G → ℝ≥0∞ := {g | cntN Γ A g = 1}.indicator (fun _ => 1)
  have hρ1m : Measurable ρ1 := measurable_const.indicator (hNm (measurableSet_singleton 1))
  have hρ1i : ∀ γ ∈ Γ, ∀ g, ρ1 (γ * g) = ρ1 g := by
    intro γ hγ g
    simp only [ρ1, Set.indicator, Set.mem_setOf_eq, cntN_mul Γ A hγ]
  have upper : ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ ≤ μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
    have e1 : ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ =
        ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g * ρ1 g⁻¹ ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hN1] with g hg
      simp [ρ1, hg]
    rw [e1, hcomp (fun g => Φ (g • y0) * cfun Γ A y0 g * ρ1 g⁻¹)
      ((hΨ.mul hcm).mul (hρ1m.comp measurable_inv)) s hs]
    calc ∫⁻ y, ∫⁻ k, Φ ((s y * (k : G)) • y0) * cfun Γ A y0 (s y * (k : G)) *
            ρ1 (s y * (k : G))⁻¹ ∂μ' ∂ν
        ≤ ∫⁻ y, Φ y * μ' 𝓕' ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hOrb] with y hy
          simp only [hΨs y hy, mul_assoc]
          rw [lintegral_const_mul (Φ y) (f := fun k : H => cfun Γ A y0 (s y * (k : G)) * ρ1 (s y * (k : G))⁻¹)
            ((hcm.comp (hmk _)).mul (hρ1m.comp (measurable_inv.comp (hmk _))))]
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [lint_fibre μ' y0 hH hAm 𝓕' h𝓕' ρ1 hρ1m hρ1i (s y)]
          calc ∫⁻ k in 𝓕', cntN Γ A ((k : G) * (s y)⁻¹) * ρ1 ((k : G) * (s y)⁻¹) ∂μ'
              ≤ ∫⁻ k in 𝓕', 1 ∂μ' := by
                refine lintegral_mono fun k => ?_
                by_cases hk : cntN Γ A ((k : G) * (s y)⁻¹) = 1
                · simp [ρ1, hk]
                · simp [ρ1, hk]
            _ = μ' 𝓕' := by rw [setLIntegral_const, one_mul]
      _ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by rw [lintegral_mul_const'' _ hΦ, mul_comm]

  let ρt : G → ℝ≥0∞ := {g | cntN Γ A g ≠ 1}.indicator (fun _ => ∞)
  have hρtm : Measurable ρt := measurable_const.indicator (hNm (measurableSet_singleton 1).compl)
  have lowerF : ∀ s0 : G, μ' 𝓕' ≤ ∫⁻ k, cfun Γ A y0 (s0 * (k : G)) + ρt (s0 * (k : G))⁻¹ ∂μ' := by
    intro s0
    have hSm : MeasurableSet {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1} :=
      (hNm.comp (measurable_inv.comp (hmk s0))) (measurableSet_singleton 1).compl
    by_cases hz : μ' {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1} = 0
    · have hae : ∀ᵐ k : H ∂μ', cntN Γ A ((k : G) * s0⁻¹) = 1 := by
        have h0 : μ' ((Inv.inv : H → H) ⁻¹' {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1}) = 0 := by
          rw [Measure.measure_preimage_inv]; exact hz
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with k hk
        by_contra h
        apply hk
        show cntN Γ A (s0 * ((k⁻¹ : H) : G))⁻¹ ≠ 1
        rwa [Subgroup.coe_inv, mul_inv_rev, inv_inv]
      calc μ' 𝓕' = ∫⁻ k in 𝓕', 1 ∂μ' := by rw [setLIntegral_const, one_mul]
        _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s0⁻¹) * (fun _ => (1 : ℝ≥0∞)) ((k : G) * s0⁻¹) ∂μ' := by
            refine lintegral_congr_ae (ae_restrict_of_ae ?_)
            filter_upwards [hae] with k hk
            rw [hk, mul_one]
        _ = ∫⁻ k, cfun Γ A y0 (s0 * (k : G)) * (fun _ => (1 : ℝ≥0∞)) ((s0 * (k : G))⁻¹) ∂μ' :=
            (lint_fibre μ' y0 hH hAm 𝓕' h𝓕' (fun _ => 1) measurable_const
              (fun _ _ _ => rfl) s0).symm
        _ ≤ ∫⁻ k, cfun Γ A y0 (s0 * (k : G)) + ρt (s0 * (k : G))⁻¹ ∂μ' :=
            lintegral_mono fun k => by rw [mul_one]; exact le_self_add
    · calc μ' 𝓕' ≤ ⊤ := le_top
        _ = ∫⁻ k, ρt (s0 * (k : G))⁻¹ ∂μ' := by
            rw [show (fun k : H => ρt (s0 * (k : G))⁻¹) =
                {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1}.indicator (fun _ => ∞) from by
                  funext k; rfl,
              lintegral_indicator_const hSm, ENNReal.top_mul hz]
        _ ≤ _ := lintegral_mono fun k => le_add_self
  have lower : μ' 𝓕' * ∫⁻ y, Φ y ∂ν ≤ ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ := by
    have e2 : ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ =
        ∫⁻ g, Φ (g • y0) * (cfun Γ A y0 g + ρt g⁻¹) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hN1] with g hg
      simp [ρt, hg]
    rw [e2, hcomp (fun g => Φ (g • y0) * (cfun Γ A y0 g + ρt g⁻¹))
      (hΨ.mul (hcm.add (hρtm.comp measurable_inv))) s hs]
    calc μ' 𝓕' * ∫⁻ y, Φ y ∂ν = ∫⁻ y, Φ y * μ' 𝓕' ∂ν := by
          rw [lintegral_mul_const'' _ hΦ, mul_comm]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hOrb] with y hy
          simp only [hΨs y hy]
          rw [lintegral_const_mul (Φ y) (f := fun k : H => cfun Γ A y0 (s y * (k : G)) + ρt (s y * (k : G))⁻¹)
            ((hcm.comp (hmk _)).add (hρtm.comp (measurable_inv.comp (hmk _))))]
          exact mul_le_mul_of_nonneg_left (lowerF (s y)) zero_le
  rw [step1]
  exact le_antisymm upper lower
end PI.VolStabW
