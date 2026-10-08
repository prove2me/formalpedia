-- Prove2me | solution 1 for SmithRegenerative.Ergodic.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:23:51.964918+00:00
-- url     : https://prove2.me/submissions/ae6c11d0-4269-4f53-91ee-3bca1e764e77

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology


namespace SmithRegenerative.Ergodic

/-- Borel–Cantelli step: for a nonnegative integrable `X` and identically distributed
`Y n ~ X`, almost surely `Y n ≤ n` eventually. -/
theorem lemma_7_bc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : ℕ → Ω → ℝ) (hXint : Integrable X P) (hXnn : 0 ≤ X)
    (hid : ∀ n, IdentDistrib (Y (n + 1)) X P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Y n ω ≤ n := by
  have hsum : (∑' j : ℕ, P {ω | X ω ∈ Set.Ioi (j : ℝ)}) < ⊤ := by
    letI : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top (Ω := Ω) hXint hXnn
  set s : ℕ → Set Ω := fun n => {ω | Y (n + 1) ω ∈ Set.Ioi ((n : ℝ) + 1)} with hs
  have hmeas : ∀ n, P (s n) ≤ P {ω | X ω ∈ Set.Ioi (n : ℝ)} := by
    intro n
    have h1 : P (s n) = P {ω | X ω ∈ Set.Ioi ((n : ℝ) + 1)} :=
      (hid n).measure_mem_eq measurableSet_Ioi
    rw [h1]
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_Ioi] at hω ⊢
    linarith
  have hsum' : (∑' n, P (s n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hsum.ne (ENNReal.tsum_le_tsum hmeas)
  filter_upwards [ae_eventually_notMem hsum'] with ω hω
  rw [Filter.eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hN m (by omega)
  simp only [hs, Set.mem_setOf_eq, Set.mem_Ioi, not_lt] at this
  push_cast
  exact this

theorem lemma_7_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hident : ∀ n, IdentDistrib (x (n + 1)) (x 1) P P)
    (hmom : Integrable (fun ω => |x 1 ω| ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0) := by
  have key : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ((k : ℝ) + 1) * |x n ω| ^ p ≤ n := by
    intro k
    have hu : Measurable (fun y : ℝ => ((k : ℝ) + 1) * |y| ^ p) := by fun_prop
    refine lemma_7_bc (fun ω => ((k : ℝ) + 1) * |x 1 ω| ^ p)
      (fun n ω => ((k : ℝ) + 1) * |x n ω| ^ p) (hmom.const_mul _) (fun ω => by positivity)
      (fun n => ?_)
    exact (hident n).comp hu
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω
  -- first: |x n|^p / n → 0
  have h1 : Tendsto (fun n : ℕ => |x n ω| ^ p / (n : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha (by positivity)
    · intro a ha
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt ha
      have h2 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
      filter_upwards [hω k, h2] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      calc |x n ω| ^ p / (n : ℝ) ≤ 1 / ((k : ℝ) + 1) := by
            rw [div_le_div_iff₀ hnpos hkpos]
            linarith
        _ < a := hk
  have h2 : Tendsto (fun n : ℕ => (|x n ω| ^ p / (n : ℝ)) ^ (1 / p)) atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => y ^ (1 / p)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (1 / p))) :=
      (Real.continuous_rpow_const (by positivity)).tendsto 0
    rw [Real.zero_rpow (by positivity)] at hc
    exact hc.comp h1
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine h2.congr fun n => ?_
  simp only [Function.comp]
  rw [Real.div_rpow (by positivity) (by positivity), one_div, Real.rpow_rpow_inv (abs_nonneg _) hp.ne',
    abs_div, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

end SmithRegenerative.Ergodic

open SmithRegenerative.Ergodic


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hindep : iIndepFun (fun n : ℕ => x (n + 1)) P)
    (hident : ∀ n, IdentDistrib (x (n + 1)) (x 1) P P)
    (hmom : Integrable (fun ω => |x 1 ω| ^ p) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => x n ω / (n : ℝ) ^ (1 / p)) atTop (𝓝 0) := by
  exact lemma_7_core x p hp hident hmom
