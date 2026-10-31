-- Prove2me | solution 1 for PoolOrNot.Moderate.theorem_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:21:17.38941+00:00
-- url     : https://prove2.me/submissions/e75d6e3a-ba74-45aa-a3b0-877a0bc9bd31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_ErlangA_Abandonment_Model
import Definitions.Def_ErlangA_Staffing_Model
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Waiting
import Theorems.Thm_PoolOrNot_Moderate_theorem_5_DQ
import Theorems.Thm_PoolOrNot_Moderate_theorem_5_PQ
import Theorems.Thm_PoolOrNot_Moderate_remark_3
import Theorems.Thm_ErlangA_Abandonment_theorem_1

open Filter Topology MeasureTheory ProbabilityTheory JSQHalfinWhitt.Tightness
open PoolOrNot.Moderate

theorem solution (μ θ ρ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n)
    (h21 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ)) atTop (𝓝 ρ))
    (hρ1 : 1 < ρ) (hρ2 : ρ < 1 + θ / μ)
    (π : (n : ℕ) → State n → ℝ)
    (hπ : ∀ n : ℕ, 1 ≤ n → IsStationaryDist (genAb n (lam n) μ θ) (π n)) :
    (∀ n : ℕ, 1 ≤ n →
      IsProbabilityMeasure (pwtLawD (π n) μ θ) ∧
      IsProbabilityMeasure (pwtLawP n (lam n) μ θ) ∧
      Integrable (fun w : ℝ => w ^ 2) (pwtLawD (π n) μ θ) ∧
      Integrable (fun w : ℝ => w ^ 2) (pwtLawP n (lam n) μ θ) ∧
      Summable (fun q : State n => π n q * ((∑' i : ℕ, (q.1 i : ℝ)) / (n : ℝ))) ∧
      Summable (fun k : ℕ => (k : ℝ) * ErlangA.Abandonment.stationaryDist n (lam n) μ θ k)) ∧
    (0 < qOf ρ μ θ ∧ qOf ρ μ θ < 1 ∧
      Tendsto (fun n : ℕ => meanOccD (π n)) atTop (𝓝 (qOf ρ μ θ + 1)) ∧
      Tendsto (fun n : ℕ => meanOccP n (lam n) μ θ) atTop (𝓝 (qOf ρ μ θ + 1))) ∧
    (Tendsto (fun n : ℕ => probAb (pwtLawD (π n) μ θ) θ) atTop (𝓝 ((ρ - 1) / ρ)) ∧
      Tendsto (fun n : ℕ => ErlangA.Abandonment.probAbandon n (lam n) μ θ) atTop
        (𝓝 ((ρ - 1) / ρ))) ∧
    (Tendsto (fun n : ℕ => meanAWT (pwtLawD (π n) μ θ) θ) atTop (𝓝 (qOf ρ μ θ / (ρ * μ))) ∧
      Tendsto (fun n : ℕ => meanAWT (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (qOf ρ μ θ / (ρ * μ)))) ∧
    (Tendsto (fun n : ℕ => probDelay (pwtLawD (π n) μ θ)) atTop
        (𝓝 (rOf ρ μ θ * (μ + θ) / (ρ * μ))) ∧
      rOf ρ μ θ * (μ + θ) / (ρ * μ) < 1 ∧
      Tendsto (fun n : ℕ => ErlangA.Staffing.probWait n (lam n) μ θ) atTop (𝓝 1)) ∧
    (Tendsto (fun n : ℕ => meanPWTDelayed (pwtLawD (π n) μ θ)) atTop (𝓝 (1 / μ)) ∧
      Real.log ρ / θ < 1 / μ ∧
      Tendsto (fun n : ℕ => meanPWTDelayed (pwtLawP n (lam n) μ θ)) atTop
        (𝓝 (Real.log ρ / θ))) ∧
    (Tendsto (fun n : ℕ => meanPWT (pwtLawD (π n) μ θ)) atTop
        (𝓝 (rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 2))) ∧
      Real.log ρ / θ < rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 2) ∧
      Tendsto (fun n : ℕ => meanPWT (pwtLawP n (lam n) μ θ)) atTop (𝓝 (Real.log ρ / θ))) ∧
    (Tendsto (fun n : ℕ => meanAWTServed (pwtLawD (π n) μ θ) θ) atTop
        (𝓝 (rOf ρ μ θ / (μ + θ))) ∧
      rOf ρ μ θ / (μ + θ) < Real.log ρ / θ ∧
      Tendsto (fun n : ℕ => meanAWTServed (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (Real.log ρ / θ))) ∧
    (Tendsto (fun n : ℕ => meanAWTAband (pwtLawD (π n) μ θ) θ) atTop (𝓝 (1 / (μ + θ))) ∧
      -(μ * (Real.log ρ / θ)) / (θ * qOf ρ μ θ) + 1 / θ < 1 / (μ + θ) ∧
      Tendsto (fun n : ℕ => meanAWTAband (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (-(μ * (Real.log ρ / θ)) / (θ * qOf ρ μ θ) + 1 / θ))) ∧
    (Tendsto (fun n : ℕ => varPWT (pwtLawD (π n) μ θ)) atTop
        (𝓝 ((rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 3)) * (2 - rOf ρ μ θ * (μ + θ) / (ρ * μ)))) ∧
      0 < (rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 3)) * (2 - rOf ρ μ θ * (μ + θ) / (ρ * μ)) ∧
      Tendsto (fun n : ℕ => varPWT (pwtLawP n (lam n) μ θ)) atTop (𝓝 0)) := by
  obtain ⟨D0, D1, D2, D3, D4, D5, D6, D7, D8, D9⟩ :=
    theorem_5_DQ μ θ ρ lam hμ hθ hlam h21 hρ1 hρ2 π hπ
  obtain ⟨P0, P1, P3, P4, P5, P6, P7, P8, P9⟩ := theorem_5_PQ μ θ ρ lam hμ hθ hlam h21 hρ1
  obtain ⟨hq0, hq1, -, -, hrq, -, -, hp1⟩ := remark_3 μ θ ρ hμ hθ hρ1 hρ2
  have hρ0 : 0 < ρ := by linarith
  -- explicit form of q
  have hqv : qOf ρ μ θ = μ * (ρ - 1) / θ := by
    unfold qOf; rw [max_eq_left (by linarith)]
  have hμρ : μ * (ρ - 1) < θ := by
    have := (lt_div_iff₀ hμ).mp (by linarith : ρ - 1 < θ / μ); linarith
  -- logarithm bounds
  have hlog_up : Real.log ρ < ρ - 1 := Real.log_lt_sub_one_of_pos hρ0 (by linarith)
  have hlog_lo : (ρ - 1) / ρ < Real.log ρ := by
    have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hρ0) (by
      intro h; have : ρ = 1 := by
        have := congrArg (·⁻¹) h; simpa using this
      linarith)
    rw [Real.log_inv] at h
    have : (ρ - 1) / ρ = 1 - ρ⁻¹ := by field_simp
    linarith
  -- key inequality μ(ρ-1)/(μ+θ) < log ρ
  have hkey : μ * (ρ - 1) / (μ + θ) < Real.log ρ := by
    refine lt_of_le_of_lt ?_ hlog_lo
    rw [div_le_div_iff₀ (by positivity) hρ0]
    nlinarith
  have hr : rOf ρ μ θ = μ * (ρ - 1) / θ := hrq.trans hqv
  -- (ii) for the pooled system, from Garnett–Mandelbaum–Reiman Theorem 1
  have hlamTop : Tendsto lam atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ) * ((n : ℝ) * μ)) atTop atTop :=
      Tendsto.pos_mul_atTop (by linarith) h21
        (Tendsto.atTop_mul_const hμ tendsto_natCast_atTop_atTop)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) * μ ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    field_simp
  have hAbP : Tendsto (fun n : ℕ => ErlangA.Abandonment.probAbandon n (lam n) μ θ) atTop
      (𝓝 ((ρ - 1) / ρ)) := by
    have h := ErlangA.Abandonment.theorem_1 μ θ lam (fun _ => θ) hμ hlam hlamTop
      (fun _ _ => hθ) hθ tendsto_const_nhds (ENNReal.ofReal ρ) (ENNReal.tendsto_ofReal h21)
    have hnot : ¬ ENNReal.ofReal ρ ≤ 1 := by
      rw [ENNReal.ofReal_le_one]; linarith
    rw [if_neg hnot] at h
    convert h using 2
    have hle : (ENNReal.ofReal ρ)⁻¹ ≤ 1 := by
      rw [ENNReal.inv_le_one, ENNReal.one_le_ofReal]; linarith
    rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hρ0.le]
    field_simp
    simp
  refine ⟨fun n hn => ⟨(D0 n hn).1, (P0 n hn).1, (D0 n hn).2.1, (P0 n hn).2.1, (D0 n hn).2.2,
      (P0 n hn).2.2⟩, ⟨hq0, hq1, D1, P1⟩, ⟨D2, hAbP⟩, ⟨D3, P3⟩, ⟨D4, hp1, P4⟩,
      ⟨D5, ?_, P5⟩, ⟨D6, ?_, P6⟩, ⟨D7, ?_, P7⟩, ⟨D8, ?_, P8⟩, ⟨D9, ?_, P9⟩⟩
  · -- log ρ / θ < 1 / μ
    rw [div_lt_div_iff₀ hθ hμ]; nlinarith
  · -- log ρ / θ < r(μ+θ)/(ρ μ²)
    rw [hr, div_lt_div_iff₀ hθ (by positivity)]
    have e : μ * (ρ - 1) / θ * (μ + θ) * θ = μ * (ρ - 1) * (μ + θ) := by field_simp
    rw [e]
    have h1 : Real.log ρ * (ρ * μ ^ 2) < (ρ - 1) * (ρ * μ ^ 2) :=
      mul_lt_mul_of_pos_right hlog_up (by positivity)
    nlinarith [mul_pos hμ (by linarith : (0:ℝ) < ρ - 1)]
  · -- r/(μ+θ) < log ρ / θ
    rw [hr, lt_div_iff₀ hθ]
    have e : μ * (ρ - 1) / θ / (μ + θ) * θ = μ * (ρ - 1) / (μ + θ) := by field_simp
    rw [e]; exact hkey
  · -- (viii) inequality
    rw [hqv]
    have hq' : 0 < ρ - 1 := by linarith
    have e : -(μ * (Real.log ρ / θ)) / (θ * (μ * (ρ - 1) / θ)) + 1 / θ
        = (1 - Real.log ρ / (ρ - 1)) / θ := by
      field_simp; ring
    rw [e, div_lt_div_iff₀ hθ (by positivity)]
    have h2 : μ * (ρ - 1) < Real.log ρ * (μ + θ) := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < μ + θ)).mp hkey; linarith
    have h3 : (1 - Real.log ρ / (ρ - 1)) * (μ + θ) * (ρ - 1)
        = ((ρ - 1) - Real.log ρ) * (μ + θ) := by field_simp
    have h4 : (1 - Real.log ρ / (ρ - 1)) * (μ + θ) < 1 * θ := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_right hc hq'.le
      rw [h3] at this
      nlinarith
    linarith
  · -- positivity of the DQ variance limit
    have hp0 : 0 < rOf ρ μ θ * (μ + θ) / (ρ * μ) := by rw [hrq]; positivity
    have : 0 < rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 3) := by rw [hrq]; positivity
    exact mul_pos this (by linarith)
