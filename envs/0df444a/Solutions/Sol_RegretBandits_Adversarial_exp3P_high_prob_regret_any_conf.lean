-- Prove2me | solution 1 for RegretBandits.Adversarial.exp3P_high_prob_regret_any_conf
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:10:25.608512+00:00
-- url     : https://prove2.me/submissions/0ebf5d3e-0830-4e10-86ea-0fa3ee0eaed5

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol
import Definitions.Def_RegretBandits_Adversarial_Exp3P
import Theorems.Thm_RegretBandits_Adversarial_exp3P_regret_general

open MeasureTheory
open RegretBandits.Adversarial

/-- The regret never exceeds `n`. -/
lemma regret_le_n_aux {K : ℕ} (n : ℕ) (g : Adversary K)
    {Ω : Type*} (I : ℕ → Ω → Fin K) (ω : Ω) :
    regret g n I ω ≤ n := by
  have hb : ∀ i, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤ n := by
    intro i
    calc ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤ ∑ t ∈ Finset.Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => (g.val_mem _ _ _).2)
      _ = n := by simp
  have h4 : 0 ≤ ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) (I t ω) :=
    Finset.sum_nonneg (fun t _ => (g.val_mem _ _ _).1)
  unfold regret
  rcases isEmpty_or_nonempty (Fin K) with h | h
  · rw [Real.iSup_of_isEmpty]
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · have h1 : (⨆ i : Fin K, ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i) ≤ n := ciSup_le hb
    linarith

theorem solution {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n)
    (g : Adversary K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P
      (exp3PProb (Real.sqrt (Real.log K / (n * K)))
        (1.05 * Real.sqrt (K * Real.log K / n))
        (0.95 * Real.sqrt (Real.log K / (n * K))) g) I)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | regret g n I ω ≤
        Real.sqrt (n * K / Real.log K) * Real.log δ⁻¹ + 5.15 * Real.sqrt (n * K * Real.log K)} := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hlog : 0 < Real.log K := Real.log_pos (by linarith)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log δ⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hδ0, hδ1⟩)
  set β : ℝ := Real.sqrt (Real.log K / (n * K)) with hβdef
  have hβpos : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hβsq : β ^ 2 = Real.log K / (n * K) := Real.sq_sqrt (by positivity)
  have hlogK : Real.log K = n * K * β ^ 2 := by rw [hβsq]; field_simp
  have e1 : Real.sqrt (K * Real.log K / n) = K * β := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ K * β)]; congr 1
    rw [mul_pow, hβsq]; field_simp
  have e2 : Real.sqrt (n * K * Real.log K) = n * K * β := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ n * K * β)]; congr 1
    rw [mul_pow, hβsq]; field_simp
  have e3 : Real.sqrt (n * K / Real.log K) = 1 / β := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / β)]; congr 1
    rw [div_pow, hβsq]; field_simp
  rw [e1] at hI
  rw [e2, e3]
  set L := Real.log δ⁻¹ with hLdef
  by_cases htriv : (n : ℝ) ≤ 5.15 * (n * K * β)
  · -- trivial regime: `R_n ≤ n`
    have : {ω | regret g n I ω ≤ 1 / β * L + 5.15 * (n * K * β)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have h1 := regret_le_n_aux n g I ω
      have h2 : 0 ≤ 1 / β * L := by positivity
      linarith
    rw [this, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  · push_neg at htriv
    have hKβ : K * β < 1 / 5.15 := by
      rw [lt_div_iff₀ (by norm_num)]
      nlinarith
    have hβsmall : β < 1 / 10.3 := by
      rw [lt_div_iff₀ (by norm_num)]
      nlinarith
    have hγ : 1.05 * (K * β) ≤ 1 / 2 := by nlinarith
    have hβηγ : (1 + β) * K * (0.95 * β) ≤ 1.05 * (K * β) := by
      have : 0 ≤ K * β := by positivity
      nlinarith
    have hmain := RegretBandits.Adversarial.exp3P_regret_general hK n hn g β (1.05 * (K * β))
      (0.95 * β) δ hβpos (by linarith) (by positivity) hγ hβηγ hδ0 hδ1 P I hI
    refine hmain.trans (measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine hω.trans (le_of_eq_of_le rfl ?_)
    have hlogmul : Real.log (K * δ⁻¹) = Real.log K + L := by
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [hlogmul, hlogK]
    have hb : 0 < n * K * β := by positivity
    have key : (n * K * β ^ 2 + L) / β = n * K * β + 1 / β * L := by field_simp
    have key2 : n * K * β ^ 2 / (0.95 * β) = n * K * β / 0.95 := by field_simp
    rw [key, key2]
    set M := n * K * β with hM
    have h1 : 0.95 * (n * K * β ^ 2) ≤ 0.0923 * M := by
      have : n * K * β ^ 2 = M * β := by rw [hM]; ring
      rw [this]; nlinarith
    have h2 : β * n * K = M := by rw [hM]; ring
    have h3 : 1.05 * (K * β) * n = 1.05 * M := by rw [hM]; ring
    have h4 : (1 + β) * (0.95 * β) * K * n = 0.95 * M + 0.95 * (n * K * β ^ 2) := by rw [hM]; ring
    have h5 : M / 0.95 ≤ 1.0527 * M := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [h2, h3, h4]
    linarith
