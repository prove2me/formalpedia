-- Prove2me | solution 1 for PI.VolStabS.lint_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:46.880927+00:00
-- url     : https://prove2.me/submissions/af3bfba9-1609-47cb-bfd3-00298496c0e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LintFibre
import Theorems.Thm_PI_VolStabS_countable_subgroupOf
import Theorems.Thm_PI_VolStabS_meas_cfun
import Theorems.Thm_PI_VolStabS_sum_rep_eq


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
  [MulAction G Y]
namespace PI.VolStabS
theorem _root_.solution {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  have : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have : MeasurableSMul ((Γ ⊓ H).subgroupOf H) H :=
    { measurable_const_smul := fun c => measurable_const_mul (c : H)
      measurable_smul_const := fun x => (measurable_mul_const x).comp measurable_subtype_coe }
  have : SMulInvariantMeasure ((Γ ⊓ H).subgroupOf H) H μ' :=
    ⟨fun c t _ => measure_preimage_mul μ' (c : H) t⟩
  have hg : Measurable fun k : H => s * (k : G)⁻¹ :=
    (measurable_const_mul s).comp (measurable_inv.comp measurable_subtype_coe)
  set F : H → ℝ≥0∞ := fun k =>
    cfun Γ A y0 (s * (k : G)⁻¹) * ρ ((s * (k : G)⁻¹)⁻¹) with hF
  have hFm : Measurable F := by
    rw [hF]
    exact ((meas_cfun Γ y0 hA).comp hg).mul (hρ.comp hg.inv)
  have hinv : ∫⁻ k, F k⁻¹ ∂μ' = ∫⁻ k, F k ∂μ' := by
    exact (Measure.measurePreserving_inv μ').lintegral_comp hFm
  have h1 : ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k, F k ∂μ' := by
    rw [← hinv]
    refine lintegral_congr fun k => ?_
    simp only [hF, InvMemClass.coe_inv, inv_inv]
  have hmem : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have hcoe : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      ((δ • k : H) : G) = ((δ : H) : G) * (k : G) := fun _ _ => rfl
  have hpt : ∀ k : H, ∑' δ : (Γ ⊓ H).subgroupOf H, F (δ • k) =
      cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) := by
    intro k
    have hδ : ∀ δ : (Γ ⊓ H).subgroupOf H, F (δ • k) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * (((δ : H) : G) * ((k : G) * s⁻¹)))) * ρ ((k : G) * s⁻¹) := by
      intro δ
      rw [← hρi _ (hmem δ) ((k : G) * s⁻¹)]
      simp only [hF, hcoe, cfun, mul_inv_rev, inv_inv, mul_assoc]
    have hrep := sum_rep_eq (Γ := Γ) y0 hH
      (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))
    simp only [mul_assoc] at hrep
    rw [tsum_congr hδ, ENNReal.tsum_mul_right, ENNReal.tsum_comm, hrep, cntN]
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, F k ∂μ' := h1
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕', F (δ • k) ∂μ' :=
      h𝓕'.lintegral_eq_tsum'' F
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H, F (δ • k) ∂μ' :=
      (lintegral_tsum fun δ => (hFm.comp (measurable_const_smul δ)).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' :=
      lintegral_congr hpt
end PI.VolStabS
