-- Prove2me | solution 1 for PoSShares.Stability.aSeq_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:18:20.270342+00:00
-- url     : https://prove2.me/submissions/42ce0ee5-bbd0-451b-81de-cbeee090fa70

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

theorem solution (ρ γ N : ℝ) (R : ℕ → ℝ) (hρ : 0 < ρ) (hγ : 1 ≤ γ) (hN : 0 < N)
    (hR : IsPowerReward ρ γ N R) :
    Tendsto (aSeq N R) atTop (𝓝 1) := by
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
  have hdecay : ∀ t, 0 ≤ 1 - aSeq N R t ∧ 1 - aSeq N R t ≤ (1 - c0) ^ t := by
    have hc01 : 0 ≤ 1 - c0 := by rw [hc0]; nlinarith
    intro t
    induction t with
    | zero => simp [aSeq_zero]
    | succ t ih =>
      obtain ⟨h0, h1⟩ := ih
      obtain ⟨hca, hcb⟩ := hc t
      have hrec : 1 - aSeq N R (t + 1) =
          (1 - (R (t + 1) / coinSupply N R (t + 1)) ^ 2) * (1 - aSeq N R t) := by
        rw [aSeq_succ]; ring
      rw [hrec, pow_succ]
      refine ⟨mul_nonneg (by linarith) h0, ?_⟩
      calc (1 - (R (t + 1) / coinSupply N R (t + 1)) ^ 2) * (1 - aSeq N R t)
          ≤ (1 - c0) * (1 - aSeq N R t) := mul_le_mul_of_nonneg_right (by linarith) h0
        _ ≤ (1 - c0) * (1 - c0) ^ t := mul_le_mul_of_nonneg_left h1 hc01
        _ = (1 - c0) ^ t * (1 - c0) := by ring
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hc0le : c0 < 1 := by rw [hc0]; nlinarith
  have hgeo : Tendsto (fun t : ℕ => (1 - c0) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h1 : Tendsto (fun t => 1 - aSeq N R t) atTop (𝓝 0) :=
    squeeze_zero (fun t => (hdecay t).1) (fun t => (hdecay t).2) hgeo
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  simpa using h2
