-- Prove2me | solution 1 for PooledRationing.MaxWeighted.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:23:41.370546+00:00
-- url     : https://prove2.me/submissions/7b9a2746-3d6f-4f2f-b07c-09eaa7b38ca1

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting
import Definitions.Def_PooledRationing_MaxWeighted_Algorithm
import Theorems.Thm_PooledRationing_MaxWeighted_display_57
import Theorems.Thm_PooledRationing_MaxWeighted_gamma_sum_L_tendsto_zero

open MeasureTheory ProbabilityTheory Filter Topology

namespace MWLemma6Aux

open PooledRationing.AsymFeas PooledRationing.MaxWeighted

theorem detCost_ge {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    {P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)} {c : Fin m → ℝ}
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (ψ : DetPolicy P c) : -K ≤ detCost F f ψ := by
  have hfc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  have hm : Measurable (fun D => f (ψ.toFun D).2) :=
    hfc.measurable.comp (measurable_snd.comp ψ.measurable')
  have hint : Integrable (fun D => f (ψ.toFun D).2) F := by
    refine Integrable.of_bound (C := K) hm.aestronglyMeasurable ?_
    filter_upwards [hf] with D hD
    simpa [Real.norm_eq_abs] using hD _ (ψ.mem' D)
  have h := integral_mono_ae (integrable_const (-K)) hint (by
    filter_upwards [hf] with D hD
    have := hD _ (ψ.mem' D)
    exact (abs_le.mp this).1)
  simpa [detCost] using h

theorem stepSize_pos (ϵ : ℝ) (T : ℕ) (hT : 1 ≤ T) : 0 < stepSize ϵ T := by
  unfold stepSize
  apply Real.rpow_pos_of_pos
  exact_mod_cast hT

theorem stepSize_tendsto (ϵ : ℝ) (hϵ : 0 < ϵ) :
    Tendsto (fun T : ℕ => stepSize ϵ T) atTop (𝓝 0) := by
  unfold stepSize
  have := (tendsto_rpow_neg_atTop (y := 1 / 2 + ϵ) (by linarith)).comp
    tendsto_natCast_atTop_atTop
  exact this

theorem T_stepSize_tendsto (ϵ : ℝ) (hϵ : ϵ < 1 / 2) :
    Tendsto (fun T : ℕ => (T : ℝ) * stepSize ϵ T) atTop atTop := by
  have h := (tendsto_rpow_atTop (y := 1 / 2 - ϵ) (by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  simp only [Function.comp, stepSize]
  rw [show (1 / 2 - ϵ) = 1 + (-(1 / 2 + ϵ)) by ring, Real.rpow_add hTp, Real.rpow_one]

end MWLemma6Aux

open MWLemma6Aux PooledRationing.AsymFeas PooledRationing.MaxWeighted

theorem solution
    {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (PooledRationing.AsymFeas.Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ) (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hc : 0 ≤ c) (hβ : ∀ j, β j ∈ Set.Ioo 0 1)
    (hF2 : MemLp id 2 F) (hDnn : ∀ᵐ D ∂F, 0 ≤ D)
    (hRmono : ∀ j d, Monotone (fun s => R j s d))
    (hRusc : ∀ j d, UpperSemicontinuous (fun s => R j s d))
    (hPcpt : ∀ D, IsCompact (P c D))
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (B : ℝ) (hA3supp : ∀ᵐ D ∂F, ∀ j, |D j| ≤ B)
    (C : ℝ) (hA3R : ∀ j s d, s ≤ d → R j s d ≤ C)
    (hPs : ∀ D, 0 ≤ D → ∀ x ∈ P c D, ∀ j, x.1 j ≤ D j)
    (K : ℝ) (hf : ∀ᵐ D ∂F, ∀ x ∈ P c D, |f x.2| ≤ K)
    (hfeas : PooledRationing.AsymFeas.IsFeasible F R β P c)
    (sel : (Fin n → ℝ) → PooledRationing.AsymFeas.DetPolicy P c)
    (hsel : ∀ w, 0 ≤ w → ∀ D, IsMinOn (PooledRationing.AsymFeas.mwsObjective f R w D) (P c D) ((sel w).toFun D))
    (hsel_meas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (sel p.1).toFun p.2))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → (Fin n → ℝ)) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (ϵ : ℝ) (hϵ : ϵ ∈ Set.Ioo 0 (1 / 2)) :
    ∀ j, ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        mwsIter sel β R (stepSize ϵ T) (fun k => Dseq k ω) T j / (T * stepSize ϵ T))
      atTop (𝓝 0) := by
  classical
  intro j
  have hnn : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ Dseq t ω := by
    rw [ae_all_iff]
    intro t
    have : ∀ᵐ D ∂(μ.map (Dseq t)), 0 ≤ D := by rw [hlaw t]; exact hDnn
    exact ae_of_ae_map (hDmeas t).aemeasurable this
  have hL := gamma_sum_L_tendsto_zero F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg
    hRmeas B hA3supp C hA3R hPs sel hsel hsel_meas μ Dseq hDmeas hindep hlaw ϵ hϵ
  filter_upwards [hnn, hL] with ω hω hLω
  set M := Gstar F f R β P c + K with hM
  set d : ℕ → Fin n → ℝ := fun k => Dseq k ω with hd
  -- the numerator of the bound
  set N : ℕ → ℝ := fun T => stepSize ϵ T * n * (1 + C) ^ 2 +
      stepSize ϵ T * ∑ t ∈ Finset.range T, Lterm F R β sel (stepSize ϵ T) T d t + 2 * M with hN
  have key : ∀ T : ℕ, 1 ≤ T →
      (mwsIter sel β R (stepSize ϵ T) d T j / (T * stepSize ϵ T)) ^ 2 ≤
        N T / (T * stepSize ϵ T) := by
    intro T hT
    set γ := stepSize ϵ T with hγdef
    have hγ : 0 < γ := stepSize_pos ϵ T hT
    have hTp : (0 : ℝ) < T := by exact_mod_cast hT
    set w := mwsIter sel β R γ d with hw
    have h57 := (display_57 F P c f R β hc hβ hF2 hDnn hRmono hRusc hPcpt hRnonneg hRmeas B
      hA3supp C hA3R hPs K hf hfeas sel hsel d (fun t => hω t) T hT γ hγ).1
    have htel : ∑ t ∈ Finset.range T, ((∑ i, (w t i) ^ 2) - (∑ i, (w (t + 1) i) ^ 2)) =
        (∑ i, (w 0 i) ^ 2) - ∑ i, (w T i) ^ 2 := by
      rw [Finset.sum_range_sub']
    have hw0 : ∑ i, (w 0 i) ^ 2 = 0 := by simp [hw, mwsIter]
    have hS : ∑ t ∈ Finset.range T,
        ((∑ i, (w t i) ^ 2) - (∑ i, (w (t + 1) i) ^ 2)
          + γ ^ 2 * n * (1 + C) ^ 2 + T * γ ^ 2 * Lterm F R β sel γ T d t) =
        - (∑ i, (w T i) ^ 2) + T * (γ ^ 2 * n * (1 + C) ^ 2)
          + T * γ ^ 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t := by
      rw [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, htel, hw0]
      simp
    rw [hS] at h57
    have hcost : (T : ℝ) * (-K) ≤ ∑ t ∈ Finset.range T, detCost F f (sel (w t)) := by
      have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) => detCost_ge F f K hf (sel (w t))
      simpa using this
    have hcost' : -K ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, detCost F f (sel (w t)) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hTp]
      linarith
    have hnorm : ∑ i, (w T i) ^ 2 ≤ T * γ * N T := by
      have h1 : -K - Gstar F f R β P c ≤ 1 / (2 * T * γ) *
          (-(∑ i, (w T i) ^ 2) + T * (γ ^ 2 * n * (1 + C) ^ 2)
            + T * γ ^ 2 * ∑ t ∈ Finset.range T, Lterm F R β sel γ T d t) := by linarith
      have h2Tγ : 0 < 2 * T * γ := by positivity
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h2Tγ] at h1
      simp only [hN, ← hγdef]
      nlinarith
    have hj : (w T j) ^ 2 ≤ ∑ i, (w T i) ^ 2 :=
      Finset.single_le_sum (f := fun i => (w T i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    have hTγ : 0 < T * γ := by positivity
    rw [div_pow, div_le_div_iff₀ (by positivity) hTγ]
    calc (w T j) ^ 2 * (T * γ) ≤ (T * γ * N T) * (T * γ) :=
          mul_le_mul_of_nonneg_right (hj.trans hnorm) hTγ.le
      _ = N T * (T * γ) ^ 2 := by ring
  -- limits
  have hNlim : Tendsto N atTop (𝓝 (0 * n * (1 + C) ^ 2 + 0 + 2 * M)) := by
    have hγl := stepSize_tendsto ϵ hϵ.1
    exact ((hγl.mul_const _).mul_const _).add hLω |>.add_const _
  have hratio : Tendsto (fun T : ℕ => N T / (T * stepSize ϵ T)) atTop (𝓝 0) :=
    hNlim.div_atTop (T_stepSize_tendsto ϵ hϵ.2)
  have hsqrt : Tendsto (fun T : ℕ => Real.sqrt (N T / (T * stepSize ϵ T))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hratio
    rw [Real.sqrt_zero] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have := stepSize_pos ϵ T hT
    have h0 : 0 ≤ mwsIter sel β R (stepSize ϵ T) d T j := by
      cases T with
      | zero => simp [mwsIter]
      | succ T => simp only [mwsIter]; exact le_max_left _ _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have := stepSize_pos ϵ T hT
    have h0 : 0 ≤ mwsIter sel β R (stepSize ϵ T) d T j := by
      cases T with
      | zero => simp [mwsIter]
      | succ T => simp only [mwsIter]; exact le_max_left _ _
    apply Real.le_sqrt_of_sq_le
    exact key T hT
