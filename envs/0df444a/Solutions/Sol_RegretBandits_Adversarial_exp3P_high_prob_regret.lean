-- Prove2me | solution 1 for RegretBandits.Adversarial.exp3P_high_prob_regret
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:12:11.052193+00:00
-- url     : https://prove2.me/submissions/6dae3476-0e39-49f8-a84c-857161c808dd

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

theorem solution {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (hn : 1 ≤ n) (g : Adversary K)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K)
    (hI : IsRun P
      (exp3PProb (Real.sqrt (Real.log (K * δ⁻¹) / (n * K)))
        (1.05 * Real.sqrt (K * Real.log K / n))
        (0.95 * Real.sqrt (Real.log K / (n * K))) g) I) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | regret g n I ω ≤ 5.15 * Real.sqrt (n * K * Real.log (K * δ⁻¹))} := by
  have hK' : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hlog : 0 < Real.log K := Real.log_pos (by linarith)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hL : 0 < Real.log δ⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hδ0, hδ1⟩)
  have hlogmul : Real.log (K * δ⁻¹) = Real.log K + Real.log δ⁻¹ := by
    rw [Real.log_mul (by positivity) (by positivity)]
  set L' := Real.log (K * δ⁻¹) with hL'def
  have hL'pos : 0 < L' := by linarith
  set β : ℝ := Real.sqrt (L' / (n * K)) with hβdef
  set β0 : ℝ := Real.sqrt (Real.log K / (n * K)) with hβ0def
  have hβpos : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hβ0pos : 0 < β0 := Real.sqrt_pos.2 (by positivity)
  have hβle : β0 ≤ β := Real.sqrt_le_sqrt (by gcongr; linarith)
  have hβsq : β ^ 2 = L' / (n * K) := Real.sq_sqrt (by positivity)
  have hβ0sq : β0 ^ 2 = Real.log K / (n * K) := Real.sq_sqrt (by positivity)
  have hlogK : Real.log K = n * K * β0 ^ 2 := by rw [hβ0sq]; field_simp
  have hL'eq : L' = n * K * β ^ 2 := by rw [hβsq]; field_simp
  have e1 : Real.sqrt (K * Real.log K / n) = K * β0 := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ K * β0)]; congr 1
    rw [mul_pow, hβ0sq]; field_simp
  have e2 : Real.sqrt (n * K * L') = n * K * β := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ n * K * β)]; congr 1
    rw [mul_pow, hβsq]; field_simp
  rw [e1] at hI
  rw [e2]
  by_cases htriv : (n : ℝ) ≤ 5.15 * (n * K * β)
  · have : {ω | regret g n I ω ≤ 5.15 * (n * K * β)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have h1 := regret_le_n_aux n g I ω
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
    have hKβ0 : K * β0 ≤ K * β := by gcongr
    have hγ : 1.05 * (K * β0) ≤ 1 / 2 := by nlinarith
    have hβηγ : (1 + β) * K * (0.95 * β0) ≤ 1.05 * (K * β0) := by
      have : 0 ≤ K * β0 := by positivity
      nlinarith
    have hmain := RegretBandits.Adversarial.exp3P_regret_general hK n hn g β (1.05 * (K * β0))
      (0.95 * β0) δ hβpos (by linarith) (by positivity) hγ hβηγ hδ0 hδ1 P I hI
    refine hmain.trans (measure_mono ?_)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine hω.trans ?_
    rw [← hL'def]
    set M := n * K * β with hM
    set M0 := n * K * β0 with hM0
    have hM0le : M0 ≤ M := by rw [hM, hM0]; gcongr
    have hM0pos : 0 < M0 := by positivity
    have k1 : L' / β = M := by rw [hL'eq, hM]; field_simp
    have k2 : Real.log K / (0.95 * β0) = M0 / 0.95 := by rw [hlogK, hM0]; field_simp
    have h2 : β * n * K = M := by rw [hM]; ring
    have h3 : 1.05 * (K * β0) * n = 1.05 * M0 := by rw [hM0]; ring
    have h4 : (1 + β) * (0.95 * β0) * K * n = 0.95 * M0 + 0.95 * β * M0 := by rw [hM0]; ring
    have hMpos : 0 < M := by positivity
    have h1 : 0.95 * β * M0 ≤ 0.0923 * M := by
      have a1 : β * M0 ≤ β * M := mul_le_mul_of_nonneg_left hM0le hβpos.le
      have a2 : β * M ≤ (1 / 10.3) * M := mul_le_mul_of_nonneg_right hβsmall.le hMpos.le
      have a3 : (1 / 10.3 : ℝ) * M * 0.95 ≤ 0.0923 * M := by norm_num; linarith
      linarith
    have h5 : M0 / 0.95 ≤ 1.0527 * M := by
      have : M0 / 0.95 = (20 / 19) * M0 := by ring
      rw [this]; linarith
    rw [k1, k2, h2, h3, h4]
    linarith
