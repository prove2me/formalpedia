-- Prove2me | solution 1 for PeriodicMAB.Upper.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:59:56.305667+00:00
-- url     : https://prove2.me/submissions/24903ade-ee65-4385-904e-d0f2fb417788

import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal



theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hindep : iIndepFun X P)
    (hX : ∀ t, HasSubgaussianMGF (X t) (σ ^ 2) P) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1) :
    P {ω | ∃ t : ℕ, 1 ≤ t ∧
        Real.sqrt (4 * (σ : ℝ) ^ 2 / t * Real.log (4 * t / δ₀)) ≤
          |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} ≤ ENNReal.ofReal δ₀ := by
  -- per-t bound
  have key : ∀ t : ℕ, P {ω | 1 ≤ t ∧
        Real.sqrt (4 * (σ : ℝ) ^ 2 / t * Real.log (4 * t / δ₀)) ≤
          |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} ≤
        ENNReal.ofReal (δ₀ ^ 2 / 8 * (1 / (t : ℝ) ^ 2)) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    set L := Real.log (4 * t / δ₀) with hL
    have hLpos : 0 < L := by
      apply Real.log_pos
      rw [lt_div_iff₀ hδ₀]; nlinarith
    set a := 4 * (σ : ℝ) ^ 2 / t * L with ha
    have ha0 : 0 ≤ a := by positivity
    set ε := (t : ℝ) * Real.sqrt a with hε
    have hε0 : 0 ≤ ε := by positivity
    have hε2 : ε ^ 2 = 4 * (σ : ℝ) ^ 2 * t * L := by
      rw [hε, mul_pow, Real.sq_sqrt ha0, ha]; field_simp
    set S : Ω → ℝ := fun ω => ∑ j ∈ Icc 1 t, X j ω with hS
    have hsub : {ω | 1 ≤ t ∧ Real.sqrt a ≤ |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} ⊆
        {ω | ε ≤ S ω} ∪ {ω | ε ≤ (fun ω => ∑ j ∈ Icc 1 t, (fun j ω => -X j ω) j ω) ω} := by
      intro ω ⟨_, hω⟩
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / t), one_div, ← div_eq_inv_mul,
        le_div_iff₀ htR] at hω
      have : ε ≤ |S ω| := by rw [hε, mul_comm]; exact hω
      rcases le_abs'.mp this with h | h
      · right; simp only [Set.mem_ofPred_eq, Finset.sum_neg_distrib]; linarith
      · left; exact h
    -- subgaussian sums
    have hsum : ∑ i ∈ Icc 1 t, (σ ^ 2 : ℝ≥0) = (t : ℝ≥0) * σ ^ 2 := by
      simp [Finset.sum_const, Nat.card_Icc]
    have hc : ((∑ i ∈ Icc 1 t, (σ ^ 2 : ℝ≥0) : ℝ≥0) : ℝ) = t * (σ : ℝ) ^ 2 := by
      rw [hsum]; push_cast; ring
    have hexp : Real.exp (-ε ^ 2 / (2 * (t * (σ : ℝ) ^ 2))) = (δ₀ / (4 * t)) ^ 2 := by
      have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
      have : -ε ^ 2 / (2 * (t * (σ : ℝ) ^ 2)) = 2 * Real.log (δ₀ / (4 * t)) := by
        rw [hε2, hL, Real.log_div (by positivity) (by positivity),
          Real.log_div (by positivity) (by positivity)]
        field_simp; ring
      rw [this, show 2 * Real.log (δ₀ / (4 * t)) = Real.log ((δ₀ / (4 * t)) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    have h1 : P.real {ω | ε ≤ S ω} ≤ (δ₀ / (4 * t)) ^ 2 := by
      have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
        (c := fun _ => σ ^ 2) (s := Icc 1 t) (fun i _ => hX i) hε0
      rw [hc, hexp] at this; exact this
    have hindep' : iIndepFun (fun j ω => -X j ω) P :=
      hindep.comp (fun _ x => -x) (fun _ => measurable_neg)
    have h2 : P.real {ω | ε ≤ (fun ω => ∑ j ∈ Icc 1 t, (fun j ω => -X j ω) j ω) ω} ≤
        (δ₀ / (4 * t)) ^ 2 := by
      have := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep'
        (c := fun _ => σ ^ 2) (s := Icc 1 t) (fun i _ => (hX i).neg) hε0
      rw [hc, hexp] at this; exact this
    calc P {ω | 1 ≤ t ∧ Real.sqrt a ≤ |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|}
        ≤ P ({ω | ε ≤ S ω} ∪ {ω | ε ≤ (fun ω => ∑ j ∈ Icc 1 t, (fun j ω => -X j ω) j ω) ω}) :=
          measure_mono hsub
      _ ≤ P {ω | ε ≤ S ω} + P {ω | ε ≤ (fun ω => ∑ j ∈ Icc 1 t, (fun j ω => -X j ω) j ω) ω} :=
          measure_union_le _ _
      _ = ENNReal.ofReal (P.real {ω | ε ≤ S ω}) +
          ENNReal.ofReal (P.real {ω | ε ≤ (fun ω => ∑ j ∈ Icc 1 t, (fun j ω => -X j ω) j ω) ω}) := by
          rw [ofReal_measureReal, ofReal_measureReal]
      _ ≤ ENNReal.ofReal ((δ₀ / (4 * t)) ^ 2) + ENNReal.ofReal ((δ₀ / (4 * t)) ^ 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
      _ = ENNReal.ofReal (δ₀ ^ 2 / 8 * (1 / (t : ℝ) ^ 2)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; field_simp; ring
  have hset : {ω | ∃ t : ℕ, 1 ≤ t ∧
        Real.sqrt (4 * (σ : ℝ) ^ 2 / t * Real.log (4 * t / δ₀)) ≤
          |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} = ⋃ t : ℕ, {ω | 1 ≤ t ∧
        Real.sqrt (4 * (σ : ℝ) ^ 2 / t * Real.log (4 * t / δ₀)) ≤
          |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} := by
    ext ω; simp
  rw [hset]
  calc _ ≤ ∑' t : ℕ, P {ω | 1 ≤ t ∧
        Real.sqrt (4 * (σ : ℝ) ^ 2 / t * Real.log (4 * t / δ₀)) ≤
          |(1 / (t : ℝ)) * ∑ j ∈ Icc 1 t, X j ω|} := measure_iUnion_le _
    _ ≤ ∑' t : ℕ, ENNReal.ofReal (δ₀ ^ 2 / 8 * (1 / (t : ℝ) ^ 2)) := ENNReal.tsum_le_tsum key
    _ = ENNReal.ofReal (δ₀ ^ 2 / 8 * (Real.pi ^ 2 / 6)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity)
          ((hasSum_zeta_two.summable).mul_left _), tsum_mul_left, hasSum_zeta_two.tsum_eq]
    _ ≤ ENNReal.ofReal δ₀ := by
        apply ENNReal.ofReal_le_ofReal
        have hpi := Real.pi_lt_d2
        have : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_pos]
        nlinarith


