-- Prove2me | solution 1 for PoSShares.Stability.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:33:25.074993+00:00
-- url     : https://prove2.me/submissions/d09d289c-aabc-49b3-80e0-09795f63baff

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology PoSShares.Stability

theorem stab_cs_succ (N₀ : ℝ) (R : ℕ → ℝ) (t : ℕ) :
    coinSupply N₀ R (t + 1) = coinSupply N₀ R t + R (t + 1) := by
  unfold coinSupply
  rw [Finset.sum_Icc_succ_top (by omega)]
  ring

theorem stab_cs_pos {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    0 < coinSupply M.N₀ M.R t := by
  induction t with
  | zero => simpa [coinSupply] using M.N₀_pos
  | succ t ih => rw [stab_cs_succ]; linarith [M.R_nonneg (t + 1)]

theorem stab_coins_bd {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    0 ≤ coins M t ω ∧ coins M t ω ≤ coinSupply M.N₀ M.R t := by
  induction t with
  | zero => simpa [coins, coinSupply] using ⟨M.n₀_nonneg, M.n₀_le⟩
  | succ t ih =>
    have hR := M.R_nonneg (t + 1)
    have hξ := M.ξ_mem (t + 1) ω
    show 0 ≤ coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω ∧
      coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω ≤ coinSupply M.N₀ M.R (t + 1)
    rw [stab_cs_succ]
    rcases hξ with h | h <;> rw [h] <;> constructor <;> nlinarith [ih.1, ih.2]

theorem stab_share_bd {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    0 ≤ share M t ω ∧ share M t ω ≤ 1 := by
  have h := stab_coins_bd M t ω
  have hp := stab_cs_pos M t
  unfold share
  exact ⟨div_nonneg h.1 hp.le, (div_le_one hp).2 h.2⟩

theorem stab_coins_sm {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable[M.ℱ t] (coins M t) := by
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    have h1 : StronglyMeasurable[M.ℱ (t + 1)] (coins M t) := ih.mono (M.ℱ.mono (Nat.le_succ t))
    exact h1.add (stronglyMeasurable_const.mul (M.ξ_meas (t + 1)))

theorem stab_share_sm {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable[M.ℱ t] (share M t) := by
  have : share M t = (coinSupply M.N₀ M.R t)⁻¹ • coins M t := by
    funext ω; simp [share, div_eq_inv_mul]
  rw [this]
  exact (stab_coins_sm M t).const_smul _

theorem stab_share_sm0 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable (share M t) := (stab_share_sm M t).mono (M.ℱ.le t)

theorem stab_xi_sm0 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) :
    StronglyMeasurable (M.ξ t) := (M.ξ_meas t).mono (M.ℱ.le t)

theorem stab_integrable_of_bd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by simpa using hC ω)

theorem stab_share_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Model Ω) (t : ℕ) : Integrable (share M t) μ :=
  stab_integrable_of_bd μ _ (stab_share_sm0 M t) 1 fun ω => by
    have := stab_share_bd M t ω
    rw [abs_of_nonneg this.1]; exact this.2

theorem stab_xi_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : Model Ω) (t : ℕ) : Integrable (M.ξ t) μ :=
  stab_integrable_of_bd μ _ (stab_xi_sm0 M t) 1 fun ω => by
    rcases M.ξ_mem t ω with h | h <;> simp [h]

theorem stab_share_succ_eq {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    share M (t + 1) ω = (1 - M.R (t + 1) / coinSupply M.N₀ M.R (t + 1)) * share M t ω +
      M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) * M.ξ (t + 1) ω := by
  have h1 := stab_cs_pos M t
  have h2 := stab_cs_pos M (t + 1)
  have h3 := stab_cs_succ M.N₀ M.R t
  unfold share
  rw [show coins M (t + 1) ω = coins M t ω + M.R (t + 1) * M.ξ (t + 1) ω from rfl]
  rw [h3] at h2 ⊢
  field_simp
  ring

theorem stab_condExp_share_succ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    μ[share M (t + 1) | M.ℱ t] =ᵐ[μ] share M t := by
  set c : ℝ := M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) with hc
  have hX : share M (t + 1) = (1 - c) • share M t + c • M.ξ (t + 1) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact stab_share_succ_eq M t ω
  have i1 := stab_share_int μ M t
  have i2 := stab_xi_int μ M (t + 1)
  have e : μ[share M t | M.ℱ t] = share M t :=
    condExp_of_stronglyMeasurable (M.ℱ.le t) (stab_share_sm M t) i1
  rw [hX]
  filter_upwards [condExp_add (μ := μ) (i1.smul (1 - c)) (i2.smul c) (M.ℱ t),
    condExp_smul (μ := μ) (1 - c) (share M t) (M.ℱ t),
    condExp_smul (μ := μ) c (M.ξ (t + 1)) (M.ℱ t), hPoS t] with ω h1 h2 h3 h4
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4, e]
  ring

theorem stab_condVar_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    condVar (M.ℱ t) (share M (t + 1)) μ =ᵐ[μ]
      fun ω => (M.R (t + 1) / coinSupply M.N₀ M.R (t + 1)) ^ 2 *
        (share M t ω * (1 - share M t ω)) := by
  set c : ℝ := M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) with hc
  have hce := stab_condExp_share_succ μ M hPoS t
  have i1 := stab_share_int μ M t
  have i2 := stab_xi_int μ M (t + 1)
  have hsm := stab_share_sm M t
  have hbd : ∀ ω, |share M t ω| ≤ 1 := fun ω => by
    have := stab_share_bd M t ω
    rw [abs_of_nonneg this.1]; exact this.2
  -- first rewrite the condVar as a conditional expectation of an explicit function
  have h1 : condVar (M.ℱ t) (share M (t + 1)) μ =ᵐ[μ]
      μ[c ^ 2 • ((fun ω => 1 - 2 * share M t ω) * M.ξ (t + 1) + fun ω => share M t ω ^ 2)
        | M.ℱ t] := by
    unfold condVar
    refine condExp_congr_ae ?_
    filter_upwards [hce] with ω hω
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hω, stab_share_succ_eq M t ω]
    rcases M.ξ_mem (t + 1) ω with h | h <;> rw [h] <;> ring
  have i3 : Integrable (fun ω => 1 - 2 * share M t ω) μ := (integrable_const _).sub (i1.const_mul 2)
  have i4 : Integrable ((fun ω => 1 - 2 * share M t ω) * M.ξ (t + 1)) μ := by
    refine stab_integrable_of_bd μ _ ((stronglyMeasurable_const.sub ((stab_share_sm0 M t).const_mul 2)).mul (stab_xi_sm0 M (t + 1))) 1 fun ω => ?_
    have := stab_share_bd M t ω
    rcases M.ξ_mem (t + 1) ω with h | h <;> simp only [Pi.mul_apply, h] <;>
      rw [abs_le] <;> constructor <;> nlinarith [this.1, this.2]
  have i5 : Integrable (fun ω => share M t ω ^ 2) μ :=
    stab_integrable_of_bd μ _ ((stab_share_sm0 M t).pow 2) 1 fun ω => by
      have := stab_share_bd M t ω
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [this.1, this.2]
  have hm1 : StronglyMeasurable[M.ℱ t] (fun ω => 1 - 2 * share M t ω) :=
    stronglyMeasurable_const.sub (hsm.const_mul 2)
  have e2 : μ[fun ω => share M t ω ^ 2 | M.ℱ t] = fun ω => share M t ω ^ 2 :=
    condExp_of_stronglyMeasurable (M.ℱ.le t) (hsm.pow 2) i5
  refine h1.trans ?_
  filter_upwards [condExp_smul (μ := μ) (c ^ 2)
      ((fun ω => 1 - 2 * share M t ω) * M.ξ (t + 1) + fun ω => share M t ω ^ 2) (M.ℱ t),
    condExp_add (μ := μ) i4 i5 (M.ℱ t),
    condExp_mul_of_stronglyMeasurable_left hm1 i4 i2, hPoS t] with ω h2 h3 h4 h5
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at h2 h3 h4 h5 ⊢
  rw [h2, h3, h4, h5, e2]
  ring

noncomputable def stabSeq (N₀ : ℝ) (R : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => stabSeq N₀ R n + (R (n + 1) / coinSupply N₀ R (n + 1)) ^ 2 * (1 - stabSeq N₀ R n)

theorem stabSeq_succ (N₀ : ℝ) (R : ℕ → ℝ) (t : ℕ) :
    stabSeq N₀ R (t + 1) =
      stabSeq N₀ R t + (R (t + 1) / coinSupply N₀ R (t + 1)) ^ 2 * (1 - stabSeq N₀ R t) := rfl

theorem stabSeq_zero (N₀ : ℝ) (R : ℕ → ℝ) : stabSeq N₀ R 0 = 0 := rfl


theorem stab_integral_share {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    ∫ ω, share M t ω ∂μ = M.n₀ / M.N₀ := by
  induction t with
  | zero => simp [share, coins, coinSupply]
  | succ t ih =>
    rw [← ih, ← integral_condExp (M.ℱ.le t) (μ := μ) (f := share M (t + 1))]
    exact integral_congr_ae (stab_condExp_share_succ μ M hPoS t)

theorem stab_share_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (t : ℕ) : MemLp (share M t) 2 μ :=
  MemLp.of_bound (stab_share_sm0 M t).aestronglyMeasurable 1 (ae_of_all _ fun ω => by
    have := stab_share_bd M t ω
    rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)

theorem stab_variance_share {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    variance (share M t) μ =
      stabSeq M.N₀ M.R t * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀)) := by
  induction t with
  | zero =>
    have : share M 0 = fun _ => M.n₀ / M.N₀ := by
      funext ω; simp [share, coins, coinSupply]
    rw [this, stabSeq_zero]
    rw [variance_eq_integral aemeasurable_const]
    simp
  | succ t ih =>
    set p : ℝ := M.n₀ / M.N₀ with hp
    set c : ℝ := M.R (t + 1) / coinSupply M.N₀ M.R (t + 1) with hc
    have hmean := stab_integral_share μ M hPoS t
    have hmem := stab_share_memLp μ M t
    have hvar := variance_eq_sub hmem
    -- law of total variance
    have htot := integral_condVar_add_variance_condExp (μ := μ) (m := M.ℱ t) (M.ℱ.le t)
      (stab_share_memLp μ M (t + 1))
    have hcv := stab_condVar_eq μ M hPoS t
    have hsq : Integrable (fun ω => share M t ω ^ 2) μ := (hmem.integrable_sq)
    have h1 : ∫ ω, (condVar (M.ℱ t) (share M (t + 1)) μ) ω ∂μ =
        c ^ 2 * (p - ∫ ω, share M t ω ^ 2 ∂μ) := by
      rw [integral_congr_ae hcv]
      have : (fun ω => c ^ 2 * (share M t ω * (1 - share M t ω))) =
          fun ω => c ^ 2 * (share M t ω - share M t ω ^ 2) := by
        funext ω; ring
      rw [this, integral_const_mul, integral_sub (stab_share_int μ M t) hsq, hmean]
    have h2 : variance (μ[share M (t + 1) | M.ℱ t]) μ = variance (share M t) μ :=
      variance_congr (stab_condExp_share_succ μ M hPoS t)
    have hE2 : ∫ ω, share M t ω ^ 2 ∂μ = variance (share M t) μ + p ^ 2 := by
      have : ∫ ω, share M t ω ^ 2 ∂μ = μ[share M t ^ 2] := rfl
      rw [this, hvar, hmean]; ring
    rw [← htot, h1, h2, hE2, ih, stabSeq_succ]
    ring

theorem stab_lim_mem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (M : Model Ω)
    (πinf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => share M t ω) atTop (𝓝 (πinf ω))) :
    ∀ᵐ ω ∂μ, πinf ω ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [hlim] with ω hω
  exact ⟨ge_of_tendsto' hω fun t => (stab_share_bd M t ω).1,
    le_of_tendsto' hω fun t => (stab_share_bd M t ω).2⟩

theorem stab_lim_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (πinf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => share M t ω) atTop (𝓝 (πinf ω))) :
    ∫ ω, πinf ω ∂μ = M.n₀ / M.N₀ := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun t => (stab_share_sm0 M t).aestronglyMeasurable) (integrable_const _)
    (fun t => ae_of_all _ fun ω => by
      have := stab_share_bd M t ω
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2) hlim
  have h2 : (fun t => ∫ ω, share M t ω ∂μ) = fun _ => M.n₀ / M.N₀ := by
    funext t; exact stab_integral_share μ M hPoS t
  rw [h2] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem stab_lim_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (πinf : Ω → ℝ) (hmeas : Measurable πinf)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => share M t ω) atTop (𝓝 (πinf ω))) :
    MemLp πinf 2 μ := by
  refine MemLp.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards [stab_lim_mem μ M πinf hlim] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2

theorem stab_variance_limit_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (M : Model Ω) (hPoS : IsPoS μ M) (πinf : Ω → ℝ)
    (hmeas : Measurable πinf)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => share M t ω) atTop (𝓝 (πinf ω))) :
    Tendsto (fun t => stabSeq M.N₀ M.R t * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀))) atTop
      (𝓝 (variance πinf μ)) := by
  have hv : (fun t => stabSeq M.N₀ M.R t * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀))) =
      fun t => (∫ ω, share M t ω ^ 2 ∂μ) - (M.n₀ / M.N₀) ^ 2 := by
    funext t
    rw [← stab_variance_share μ M hPoS t, variance_eq_sub (stab_share_memLp μ M t)]
    have : μ[share M t ^ 2] = ∫ ω, share M t ω ^ 2 ∂μ := rfl
    rw [this, stab_integral_share μ M hPoS t]
  rw [hv, variance_eq_sub (stab_lim_memLp μ M πinf hmeas hlim)]
  have hmean := stab_lim_mean μ M hPoS πinf hlim
  have h : Tendsto (fun t => ∫ ω, share M t ω ^ 2 ∂μ) atTop (𝓝 (∫ ω, πinf ω ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
      (fun t => ((stab_share_sm0 M t).pow 2).aestronglyMeasurable) (integrable_const _)
      (fun t => ae_of_all _ fun ω => ?_) ?_
    · have := stab_share_bd M t ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [this.1, this.2]
    · filter_upwards [hlim] with ω hω
      exact hω.pow 2
  have : μ[πinf ^ 2] = ∫ ω, πinf ω ^ 2 ∂μ := rfl
  rw [this, hmean]
  exact h.sub_const _

theorem stab_key (γ a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : γ ≤ 1) :
    b ^ (γ - 1) + (1 - γ) * b ^ (γ - 2) * (b - a) ≤ a ^ (γ - 1) := by
  have hb2 : b ^ (γ - 2) = b ^ (γ - 1) / b := by
    rw [show γ - 2 = (γ - 1) - 1 by ring, Real.rpow_sub_one hb.ne']
  have hlog : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hlog
  have hexp : 1 + (γ - 1) * (Real.log a - Real.log b) ≤
      Real.exp ((γ - 1) * (Real.log a - Real.log b)) := by
    linarith [Real.add_one_le_exp ((γ - 1) * (Real.log a - Real.log b))]
  have hA : a ^ (γ - 1) = b ^ (γ - 1) * Real.exp ((γ - 1) * (Real.log a - Real.log b)) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    congr 1; ring
  have hbp : 0 < b ^ (γ - 1) := Real.rpow_pos_of_pos hb _
  rw [hA, hb2]
  have h1 : (1 - γ) * (1 - a / b) ≤ (γ - 1) * (Real.log a - Real.log b) := by
    nlinarith
  have h2 : 1 + (1 - γ) * (1 - a / b) ≤ Real.exp ((γ - 1) * (Real.log a - Real.log b)) := by
    linarith
  calc b ^ (γ - 1) + (1 - γ) * (b ^ (γ - 1) / b) * (b - a)
      = b ^ (γ - 1) * (1 + (1 - γ) * (1 - a / b)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hbp.le

theorem stab_lemma5 (ρ γ N : ℝ) (R : ℕ → ℝ) (hρ : 0 < ρ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hN : 0 < N)
    (hR : IsPowerReward ρ γ N R) :
    ∀ t : ℕ, 1 ≤ t → stabSeq N R (t + 1) ≤ ρ / (1 - γ) * N ^ (γ - 1) := by
  obtain ⟨hγ0, hγ1⟩ := hγ
  have hs : ∀ t, N ≤ coinSupply N R t := by
    intro t
    induction t with
    | zero => simp [coinSupply]
    | succ t ih =>
      have h1 : R (t + 1) = ρ * coinSupply N R t ^ γ := by simpa using hR (t + 1) (by omega)
      have : 0 ≤ R (t + 1) := by
        rw [h1]; exact mul_nonneg hρ.le (Real.rpow_nonneg (by linarith) _)
      rw [stab_cs_succ]; linarith
  have hK : 0 < ρ / (1 - γ) := div_pos hρ (by linarith)
  -- one step
  have hstep : ∀ k, (R (k + 1) / coinSupply N R (k + 1)) ^ 2 ≤
      ρ / (1 - γ) * (coinSupply N R k ^ (γ - 1) - coinSupply N R (k + 1) ^ (γ - 1)) := by
    intro k
    have hsk : 0 < coinSupply N R k := lt_of_lt_of_le hN (hs k)
    have h1 : R (k + 1) = ρ * coinSupply N R k ^ γ := by simpa using hR (k + 1) (by omega)
    have hRpos : 0 < R (k + 1) := by rw [h1]; exact mul_pos hρ (Real.rpow_pos_of_pos hsk _)
    have hsuc := stab_cs_succ N R k
    have hS : 0 < coinSupply N R (k + 1) := by rw [hsuc]; linarith
    have key := stab_key γ (coinSupply N R k) (coinSupply N R (k + 1)) hsk hS hγ1.le
    have hdiff : coinSupply N R (k + 1) - coinSupply N R k = R (k + 1) := by rw [hsuc]; ring
    rw [hdiff] at key
    have hb2 : coinSupply N R (k + 1) ^ (γ - 2) =
        coinSupply N R (k + 1) ^ γ / coinSupply N R (k + 1) ^ 2 := by
      rw [Real.rpow_sub hS, Real.rpow_two]
    rw [hb2] at key
    have hmono : coinSupply N R k ^ γ ≤ coinSupply N R (k + 1) ^ γ :=
      Real.rpow_le_rpow hsk.le (by rw [hsuc]; linarith) hγ0
    have hleft : ρ * (coinSupply N R (k + 1) ^ γ / coinSupply N R (k + 1) ^ 2) * R (k + 1) ≤
        ρ / (1 - γ) * (coinSupply N R k ^ (γ - 1) - coinSupply N R (k + 1) ^ (γ - 1)) := by
      have hpos : 0 < 1 - γ := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith [mul_le_mul_of_nonneg_left key hρ.le]
    refine le_trans ?_ hleft
    rw [div_pow]
    have hS2 : 0 < coinSupply N R (k + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hS2]
    have : R (k + 1) * R (k + 1) = R (k + 1) * (ρ * coinSupply N R k ^ γ) := by rw [← h1]
    calc R (k + 1) ^ 2 = R (k + 1) * (ρ * coinSupply N R k ^ γ) := by rw [sq, ← h1]
      _ ≤ R (k + 1) * (ρ * coinSupply N R (k + 1) ^ γ) := by
          apply mul_le_mul_of_nonneg_left _ hRpos.le
          exact mul_le_mul_of_nonneg_left hmono hρ.le
      _ = _ := by field_simp
  -- accumulate
  have hacc : ∀ n, stabSeq N R n ∈ Set.Icc (0 : ℝ) 1 ∧
      stabSeq N R n ≤ ρ / (1 - γ) * (N ^ (γ - 1) - coinSupply N R n ^ (γ - 1)) := by
    intro n
    induction n with
    | zero => simp [stabSeq_zero, coinSupply]
    | succ n ih =>
      obtain ⟨⟨h0, h1⟩, h2⟩ := ih
      have hc := hstep n
      have hc0 : 0 ≤ (R (n + 1) / coinSupply N R (n + 1)) ^ 2 := sq_nonneg _
      have hsn : 0 < coinSupply N R n := lt_of_lt_of_le hN (hs n)
      have hsn1 := hstep n
      have hunit : (R (n + 1) / coinSupply N R (n + 1)) ^ 2 ≤ 1 := by
        have hsuc := stab_cs_succ N R n
        have hRn : 0 ≤ R (n + 1) := by
          have h1 : R (n + 1) = ρ * coinSupply N R n ^ γ := by simpa using hR (n + 1) (by omega)
          rw [h1]; exact mul_nonneg hρ.le (Real.rpow_nonneg hsn.le _)
        have hS : 0 < coinSupply N R (n + 1) := by rw [hsuc]; linarith
        have : R (n + 1) / coinSupply N R (n + 1) ≤ 1 := by
          rw [div_le_one hS, hsuc]; linarith
        have h0' : 0 ≤ R (n + 1) / coinSupply N R (n + 1) := div_nonneg hRn hS.le
        nlinarith
      rw [stabSeq_succ]
      refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
      nlinarith
  intro t _
  have := (hacc (t + 1)).2
  have hp : 0 ≤ ρ / (1 - γ) * coinSupply N R (t + 1) ^ (γ - 1) :=
    mul_nonneg hK.le (Real.rpow_nonneg (lt_of_lt_of_le hN (hs _)).le _)
  nlinarith

theorem stab_stabSeq_tendsto_one (ρ γ N : ℝ) (R : ℕ → ℝ) (hρ : 0 < ρ) (hγ : 1 ≤ γ) (hN : 0 < N)
    (hR : IsPowerReward ρ γ N R) :
    Tendsto (stabSeq N R) atTop (𝓝 1) := by
  -- supply bounded below by N
  have hs : ∀ t, N ≤ coinSupply N R t := by
    intro t
    induction t with
    | zero => simp [coinSupply]
    | succ t ih =>
      have h1 : R (t + 1) = ρ * coinSupply N R t ^ γ := by simpa using hR (t + 1) (by omega)
      have : 0 ≤ R (t + 1) := by
        rw [h1]; exact mul_nonneg hρ.le (Real.rpow_nonneg (by linarith) _)
      rw [stab_cs_succ]; linarith
  set k : ℝ := ρ * N ^ (γ - 1) with hk
  have hkpos : 0 < k := mul_pos hρ (Real.rpow_pos_of_pos hN _)
  set q : ℝ := k / (1 + k) with hq
  have hqpos : 0 < q := div_pos hkpos (by linarith)
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  set c0 : ℝ := q ^ 2 with hc0
  -- coefficient bounds
  have hc : ∀ t, c0 ≤ (R (t + 1) / coinSupply N R (t + 1)) ^ 2 ∧
      (R (t + 1) / coinSupply N R (t + 1)) ^ 2 ≤ 1 := by
    intro t
    have hst : 0 < coinSupply N R t := lt_of_lt_of_le hN (hs t)
    have h1 : R (t + 1) = ρ * coinSupply N R t ^ γ := by simpa using hR (t + 1) (by omega)
    have hpow : coinSupply N R t ^ γ = coinSupply N R t ^ (γ - 1) * coinSupply N R t := by
      rw [Real.rpow_sub_one hst.ne']
      field_simp
    have hle : N ^ (γ - 1) ≤ coinSupply N R t ^ (γ - 1) :=
      Real.rpow_le_rpow hN.le (hs t) (by linarith)
    have hRk : k * coinSupply N R t ≤ R (t + 1) := by
      rw [h1, hpow, hk]
      have := mul_le_mul_of_nonneg_right hle hst.le
      nlinarith [mul_le_mul_of_nonneg_left this hρ.le]
    have hRpos : 0 < R (t + 1) := lt_of_lt_of_le (mul_pos hkpos hst) hRk
    have hsuc := stab_cs_succ N R t
    have hSpos : 0 < coinSupply N R (t + 1) := by rw [hsuc]; linarith
    have hr0 : 0 ≤ R (t + 1) / coinSupply N R (t + 1) := div_nonneg hRpos.le hSpos.le
    have hr1 : R (t + 1) / coinSupply N R (t + 1) ≤ 1 := by
      rw [div_le_one hSpos, hsuc]; linarith
    have hrq : q ≤ R (t + 1) / coinSupply N R (t + 1) := by
      rw [hq, div_le_div_iff₀ (by linarith) hSpos, hsuc]
      nlinarith
    refine ⟨?_, ?_⟩
    · rw [hc0]; exact pow_le_pow_left₀ hqpos.le hrq 2
    · nlinarith
  -- geometric decay of 1 - a_t
  have hdecay : ∀ t, 0 ≤ 1 - stabSeq N R t ∧ 1 - stabSeq N R t ≤ (1 - c0) ^ t := by
    have hc01 : 0 ≤ 1 - c0 := by rw [hc0]; nlinarith
    intro t
    induction t with
    | zero => simp [stabSeq_zero]
    | succ t ih =>
      obtain ⟨h0, h1⟩ := ih
      obtain ⟨hca, hcb⟩ := hc t
      have hrec : 1 - stabSeq N R (t + 1) =
          (1 - (R (t + 1) / coinSupply N R (t + 1)) ^ 2) * (1 - stabSeq N R t) := by
        rw [stabSeq_succ]; ring
      rw [hrec, pow_succ]
      refine ⟨mul_nonneg (by linarith) h0, ?_⟩
      calc (1 - (R (t + 1) / coinSupply N R (t + 1)) ^ 2) * (1 - stabSeq N R t)
          ≤ (1 - c0) * (1 - stabSeq N R t) := mul_le_mul_of_nonneg_right (by linarith) h0
        _ ≤ (1 - c0) * (1 - c0) ^ t := mul_le_mul_of_nonneg_left h1 hc01
        _ = (1 - c0) ^ t * (1 - c0) := by ring
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hc0le : c0 < 1 := by rw [hc0]; nlinarith
  have hgeo : Tendsto (fun t : ℕ => (1 - c0) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h1 : Tendsto (fun t => 1 - stabSeq N R t) atTop (𝓝 0) :=
    squeeze_zero (fun t => (hdecay t).1) (fun t => (hdecay t).2) hgeo
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  simpa using h2

theorem stab_eqA31 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π₁ ε : ℝ) (X : Ω → ℝ) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1) (hX : Measurable X)
    (hX01 : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∫ ω, X ω ∂μ = π₁)
    (hvar : variance X μ = π₁ * (1 - π₁))
    (hε : ε ∈ Set.Ioo (0 : ℝ) (Real.sqrt (π₁ * (1 - π₁)))) :
    (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) ≤ μ.real {ω | ε < |X ω - π₁|} ∧
      0 < (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) := by
  obtain ⟨h0, h1⟩ := hπ₁
  obtain ⟨he0, he1⟩ := hε
  have hv : 0 < π₁ * (1 - π₁) := mul_pos h0 (by linarith)
  have hv4 : π₁ * (1 - π₁) ≤ 1 / 4 := by nlinarith [sq_nonneg (π₁ - 1/2)]
  have hε2 : ε ^ 2 < π₁ * (1 - π₁) := by
    have := Real.sq_sqrt hv.le
    nlinarith
  have hden : 0 < 1 - ε ^ 2 := by linarith
  have hpos : 0 < (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) :=
    div_pos (by linarith) hden
  refine ⟨?_, hpos⟩
  set A : Set Ω := {ω | ε < |X ω - π₁|} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const ((hX.sub measurable_const).abs)
  have hmeanX : μ[X] = π₁ := hmean
  have hvi : variance X μ = ∫ ω, (X ω - π₁) ^ 2 ∂μ := by
    rw [variance_eq_integral hX.aemeasurable, hmeanX]
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂μ, (X ω - π₁) ^ 2 ≤ ε ^ 2 + (1 - ε ^ 2) * A.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hX01] with ω hω
    obtain ⟨hω0, hω1⟩ := hω
    by_cases hm : ω ∈ A
    · rw [Set.indicator_of_mem hm]
      have : (X ω - π₁) ^ 2 ≤ 1 := by nlinarith
      linarith
    · rw [Set.indicator_of_notMem hm]
      have : |X ω - π₁| ≤ ε := not_lt.mp hm
      have h2 : (X ω - π₁) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      linarith
  have hint1 : Integrable (fun ω => (X ω - π₁) ^ 2) μ := by
    have hb : ∀ᵐ ω ∂μ, ‖(X ω - π₁) ^ 2‖ ≤ 1 := by
      filter_upwards [hX01] with ω hω
      obtain ⟨hω0, hω1⟩ := hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    exact Integrable.of_bound ((hX.sub measurable_const).pow_const 2).aestronglyMeasurable 1 hb
  have hind : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hint2 : Integrable (fun ω => ε ^ 2 + (1 - ε ^ 2) * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add (hind.const_mul _)
  have hle := integral_mono_ae hint1 hint2 hpt
  have hcalc : ∫ ω, (ε ^ 2 + (1 - ε ^ 2) * A.indicator (fun _ => (1 : ℝ)) ω) ∂μ
      = ε ^ 2 + (1 - ε ^ 2) * μ.real A := by
    rw [integral_add (integrable_const _) (hind.const_mul _), integral_const_mul,
      integral_indicator hAm]
    simp
  rw [← hvi, hvar] at hle
  rw [hcalc] at hle
  rw [div_le_iff₀ hden]
  nlinarith

theorem stab_lemma6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π₁ : ℝ) (M : ℕ → Model Ω) (hPoS : ∀ N, IsPoS μ (M N))
    (hN : ∀ N : ℕ, 1 ≤ N → (M N).N₀ = N) (hn : ∀ N, (M N).n₀ = π₁ * (M N).N₀)
    (πinf : ℕ → Ω → ℝ) (hmeas : ∀ N, Measurable (πinf N))
    (hlim : ∀ N, ∀ᵐ ω ∂μ, Tendsto (fun t => share (M N) t ω) atTop (𝓝 (πinf N ω)))
    (hvar : Tendsto (fun N => variance (πinf N) μ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => μ.real {ω | ε ≤ |πinf N ω - π₁|}) atTop (𝓝 0) := by
  intro ε hε
  have hmean : ∀ N, ∫ ω, πinf N ω ∂μ = π₁ := by
    intro N
    rw [stab_lim_mean μ (M N) (hPoS N) (πinf N) (hlim N), hn N]
    have := (M N).N₀_pos
    field_simp
  have hcheb : ∀ N, μ.real {ω | ε ≤ |πinf N ω - π₁|} ≤ variance (πinf N) μ / ε ^ 2 := by
    intro N
    have h := meas_ge_le_variance_div_sq (μ := μ) (stab_lim_memLp μ (M N) (πinf N) (hmeas N) (hlim N)) hε
    have hm : μ[πinf N] = π₁ := hmean N
    rw [hm] at h
    have hnn : 0 ≤ variance (πinf N) μ / ε ^ 2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
    rw [measureReal_def]
    calc (μ {ω | ε ≤ |πinf N ω - π₁|}).toReal
        ≤ (ENNReal.ofReal (variance (πinf N) μ / ε ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = _ := ENNReal.toReal_ofReal hnn
  refine squeeze_zero (fun N => measureReal_nonneg) hcheb ?_
  simpa using hvar.div_const (ε ^ 2)


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ γ π₁ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1)
    (M : ℕ → Model Ω) (hPoS : ∀ N, IsPoS μ (M N))
    (hN : ∀ N : ℕ, 1 ≤ N → (M N).N₀ = N) (hn : ∀ N, (M N).n₀ = π₁ * (M N).N₀)
    (hR : ∀ N, IsPowerReward ρ γ (M N).N₀ (M N).R)
    (πinf : ℕ → Ω → ℝ) (hmeas : ∀ N, Measurable (πinf N))
    (hlim : ∀ N, ∀ᵐ ω ∂μ, Tendsto (fun t => share (M N) t ω) atTop (𝓝 (πinf N ω))) :
    (∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => μ.real {ω | ε ≤ |πinf N ω - π₁|}) atTop (𝓝 0)) ↔ γ < 1 := by
  have hπ₁' := hπ₁
  obtain ⟨hπ0, hπ1⟩ := hπ₁
  have hv : 0 < π₁ * (1 - π₁) := mul_pos hπ0 (by linarith)
  have hN0 : ∀ N, (M N).n₀ / (M N).N₀ = π₁ := fun N => by
    have := (M N).N₀_pos
    rw [hn N]; field_simp
  have hmean : ∀ N, ∫ ω, πinf N ω ∂μ = π₁ := fun N => by
    rw [stab_lim_mean μ (M N) (hPoS N) (πinf N) (hlim N), hN0 N]
  have hT : ∀ N, Tendsto (fun t => stabSeq (M N).N₀ (M N).R t * (π₁ * (1 - π₁))) atTop
      (𝓝 (variance (πinf N) μ)) := fun N => by
    have := stab_variance_limit_eq μ (M N) (hPoS N) (πinf N) (hmeas N) (hlim N)
    simpa only [hN0 N] using this
  constructor
  · intro h
    by_contra hγlt
    replace hγlt : 1 ≤ γ := not_lt.mp hγlt
    have hvar : ∀ N, variance (πinf N) μ = π₁ * (1 - π₁) := by
      intro N
      have hA := stab_stabSeq_tendsto_one ρ γ (M N).N₀ (M N).R hρ hγlt (M N).N₀_pos (hR N)
      have := tendsto_nhds_unique (hT N) (hA.mul_const (π₁ * (1 - π₁)))
      simpa using this
    set ε : ℝ := Real.sqrt (π₁ * (1 - π₁)) / 2 with hε
    have hsq : 0 < Real.sqrt (π₁ * (1 - π₁)) := Real.sqrt_pos.2 hv
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hε1 : ε < Real.sqrt (π₁ * (1 - π₁)) := by rw [hε]; linarith
    have hc : 0 < (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) :=
      (stab_eqA31 μ π₁ ε (πinf 0) hπ₁' (hmeas 0)
        (stab_lim_mem μ (M 0) (πinf 0) (hlim 0)) (hmean 0) (hvar 0) ⟨hε0, hε1⟩).2
    obtain ⟨N, hN'⟩ := ((h ε hε0).eventually (gt_mem_nhds hc)).exists
    have hlow := (stab_eqA31 μ π₁ ε (πinf N) hπ₁' (hmeas N)
        (stab_lim_mem μ (M N) (πinf N) (hlim N)) (hmean N) (hvar N) ⟨hε0, hε1⟩).1
    have hsub : μ.real {ω | ε < |πinf N ω - π₁|} ≤ μ.real {ω | ε ≤ |πinf N ω - π₁|} :=
      measureReal_mono (Set.setOf_subset_setOf.2 fun ω hω => le_of_lt hω)
    linarith
  · intro hγ1
    have hvar0 : Tendsto (fun N => variance (πinf N) μ) atTop (𝓝 0) := by
      have hbound : ∀ N : ℕ, 1 ≤ N → variance (πinf N) μ ≤
          ρ / (1 - γ) * (N : ℝ) ^ (γ - 1) * (π₁ * (1 - π₁)) := by
        intro N hN1
        have hT' := (tendsto_add_atTop_iff_nat 1).2 (hT N)
        refine le_of_tendsto hT' (eventually_atTop.2 ⟨1, fun t ht => ?_⟩)
        have h5 := stab_lemma5 ρ γ (M N).N₀ (M N).R hρ ⟨hγ.le, hγ1⟩ (M N).N₀_pos (hR N) t ht
        have h6 : (N : ℝ) ^ (γ - 1) = (M N).N₀ ^ (γ - 1) := by rw [hN N hN1]
        rw [h6]
        exact mul_le_mul_of_nonneg_right h5 hv.le
      have hz : Tendsto (fun N : ℕ => ρ / (1 - γ) * (N : ℝ) ^ (γ - 1) * (π₁ * (1 - π₁)))
          atTop (𝓝 0) := by
        have h0 : Tendsto (fun x : ℝ => x ^ (-(1 - γ))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by linarith)
        have h1 := h0.comp tendsto_natCast_atTop_atTop
        have h2 := (h1.const_mul (ρ / (1 - γ))).mul_const (π₁ * (1 - π₁))
        simp only [mul_zero, zero_mul] at h2
        convert h2 using 3
        simp only [Function.comp]
        ring_nf
      exact squeeze_zero' (Eventually.of_forall fun N => variance_nonneg _ _)
        (eventually_atTop.2 ⟨1, hbound⟩) hz
    exact stab_lemma6 μ π₁ M hPoS hN hn πinf hmeas hlim hvar0
