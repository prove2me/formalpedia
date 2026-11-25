-- Prove2me | solution 1 for PI.VolStabW.lint_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:41.001235+00:00
-- url     : https://prove2.me/submissions/eae99b19-3579-41f0-aa12-f820d5de282d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LintFibre
import Theorems.Thm_PI_VolStabW_countable_subgroupOf
import Theorems.Thm_PI_VolStabW_sum_rep_eq


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
  [MulAction G Y]
namespace PI.VolStabW
theorem _root_.solution {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  haveI : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have memΓ : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have h1 : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := by
    intro δ k
    have e : (((δ • k)⁻¹ : H) : G) = (k : G)⁻¹ * ((δ : H) : G)⁻¹ := by
      show ((((δ : H) * k)⁻¹ : H) : G) = _
      rw [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev]
    rw [e]
    have eρ : ρ ((s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹) = ρ ((k : G) * s⁻¹) := by
      rw [show (s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹ = ((δ : H) : G) * ((k : G) * s⁻¹) by group]
      exact hρi _ (memΓ δ) _
    rw [eρ]
    congr 1
    unfold cfun
    refine tsum_congr fun x => ?_
    congr 1
    group
  have hm : ∀ δ : (Γ ⊓ H).subgroupOf H, Measurable fun k : H =>
      (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := fun δ =>
    (Measurable.ennreal_tsum fun _ => (measurable_const.indicator hA).comp
      ((measurable_const_mul _).comp ((measurable_mul_const _).comp measurable_subtype_coe))).mul
      (hρ.comp ((measurable_mul_const _).comp measurable_subtype_coe))
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, cfun Γ A y0 (s * ((k⁻¹ : H) : G)) * ρ ((s * ((k⁻¹ : H) : G))⁻¹) ∂μ' :=
        (lintegral_inv_eq_self
          (fun k : H => cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹))).symm
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) ∂μ' :=
        h𝓕'.lintegral_eq_tsum'' _
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        tsum_congr fun δ => lintegral_congr fun k => h1 δ k
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H,
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        (lintegral_tsum fun δ => (hm δ).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
        refine lintegral_congr fun k => ?_
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
        congr 1
        exact sum_rep_eq y0 hH (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))
end PI.VolStabW
