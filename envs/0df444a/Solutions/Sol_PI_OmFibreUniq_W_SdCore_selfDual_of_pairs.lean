-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdCore.selfDual_of_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:57.394671+00:00
-- url     : https://prove2.me/submissions/6a58cee2-fbc8-4ea0-aebd-c14e7d3039f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_zero_mem_ann
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_exists_normalized
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
namespace PI.OmFibreUniq.W.SdCore
theorem _root_.solution (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1)
    (M : ℕ → AddSubgroup V) (hMc : ∀ k, IsCompact (M k : Set V)) (hMo : ∀ k, IsOpen (M k : Set V))
    (hNc : ∀ k, IsCompact (ann χ (M k))) (hNo : ∀ k, IsOpen (ann χ (M k)))
    (hex : ∀ y, ∀ᶠ k in atTop, y ∈ M k)
    (hsh : ∀ U ∈ 𝓝 (0 : V), ∀ᶠ k in atTop, ann χ (M k) ⊆ U)
    (μ0 : Measure V) [μ0.IsAddHaarMeasure]
    (hconst : ∀ k, μ0 (M k) * μ0 (ann χ (M k)) = μ0 (M 0) * μ0 (ann χ (M 0))) :
    ∃ μ : Measure V, SelfDual μ χ := by
  obtain ⟨μ, hμ, hprod⟩ := exists_normalized μ0 (fun k => (M k : Set V)) (fun k => ann χ (M k))
    hMc hNc (hMo 0) (hNo 0) ⟨0, (M 0).zero_mem⟩ ⟨0, zero_mem_ann χ hχ hsym hn _⟩ hconst
  refine ⟨μ, hμ, fun Φ hc hs hI z => ?_⟩
  set I : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hIdef
  have hL : Tendsto (fun k => ∫ y, (M k : Set V).indicator (fun y => I y * χ y z) y ∂μ) atTop
      (𝓝 (∫ y, I y * χ y z ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖I y‖) (fun k => ?_) hI.norm
      (fun k => ?_) ?_
    · exact (hI.aestronglyMeasurable.mul
        (hχc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).indicator
        (hMo k).measurableSet
    · filter_upwards with y
      by_cases hy : y ∈ (M k : Set V)
      · simp [Set.indicator_of_mem hy, norm_mul, hn]
      · simp [Set.indicator_of_notMem hy]
    · filter_upwards with y
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hex y] with k hk
      simp [Set.indicator_of_mem (SetLike.mem_coe.2 hk)]
  have hR : Tendsto (fun k => (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), Φ (u - z) ∂μ) atTop
      (𝓝 (Φ (-z))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hcz : Continuous (fun u => Φ (u - z)) := hc.comp (continuous_id.sub continuous_const)
    have hU : {u : V | dist (Φ (u - z)) (Φ (-z)) < ε / 2} ∈ 𝓝 (0 : V) := by
      have h0 : Φ ((0 : V) - z) = Φ (-z) := by rw [zero_sub]
      exact hcz.continuousAt.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (half_pos hε))
    filter_upwards [hsh _ hU] with k hk
    have hmn := hprod k
    have hfin : μ (ann χ (M k)) < ⊤ := (hNc k).measure_lt_top
    have hio : IntegrableOn (fun u => Φ (u - z)) (ann χ (M k)) μ := hcz.continuousOn.integrableOn_compact (hNc k)
    have e : (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), Φ (u - z) ∂μ - Φ (-z) =
        (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), (Φ (u - z) - Φ (-z)) ∂μ := by
      rw [integral_sub hio (integrableOn_const hfin.ne), setIntegral_const, mul_sub]
      congr 1
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hmn, Complex.ofReal_one, one_mul]
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have hb : ‖∫ u in ann χ (M k), (Φ (u - z) - Φ (-z)) ∂μ‖ ≤ ε / 2 * μ.real (ann χ (M k)) := by
      refine norm_setIntegral_le_of_norm_le_const hfin fun u hu => ?_
      have := hk hu
      simp only [Set.mem_setOf_eq, dist_eq_norm] at this
      exact this.le
    calc μ.real (M k : Set V) * ‖∫ u in ann χ (M k), (Φ (u - z) - Φ (-z)) ∂μ‖
        ≤ μ.real (M k : Set V) * (ε / 2 * μ.real (ann χ (M k))) :=
          mul_le_mul_of_nonneg_left hb measureReal_nonneg
      _ = ε / 2 := by rw [mul_comm (ε / 2), ← mul_assoc, hmn, one_mul]
      _ < ε := half_lt_self hε
  have hEq : (fun k => ∫ y, (M k : Set V).indicator (fun y => I y * χ y z) y ∂μ) =
      fun k => (μ.real (M k : Set V) : ℂ) * ∫ u in ann χ (M k), Φ (u - z) ∂μ := by
    funext k
    rw [integral_indicator (hMo k).measurableSet]
    exact key χ hχc hχ hsym hn μ (M k) (hMc k) (hMo k) Φ hc hs z
  rw [hEq] at hL
  exact tendsto_nhds_unique hL hR
end PI.OmFibreUniq.W.SdCore
