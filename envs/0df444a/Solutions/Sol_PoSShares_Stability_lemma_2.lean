-- Prove2me | solution 1 for PoSShares.Stability.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:23:51.145159+00:00
-- url     : https://prove2.me/submissions/986a5993-f7ed-4da7-89ce-1418ef4b3e03

import Mathlib
import Definitions.Def_PoSShares_Stability_Model
import Definitions.Def_PoSShares_Stability_VarianceSeq

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
      aSeq M.N₀ M.R t * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀)) := by
  induction t with
  | zero =>
    have : share M 0 = fun _ => M.n₀ / M.N₀ := by
      funext ω; simp [share, coins, coinSupply]
    rw [this, aSeq_zero]
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
    rw [← htot, h1, h2, hE2, ih, aSeq_succ]
    ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : Model Ω) (hPoS : IsPoS μ M) (t : ℕ) :
    variance (share M (t + 1)) μ =
      aSeq M.N₀ M.R (t + 1) * (M.n₀ / M.N₀ * (1 - M.n₀ / M.N₀)) :=
  stab_variance_share μ M hPoS (t + 1)
