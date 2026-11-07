-- Prove2me | solution 1 for WolffPASTA.Main.arrival_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:12:07.892286+00:00
-- url     : https://prove2.me/submissions/269b2162-019b-4544-8831-aa5c022e081c

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Nat

namespace WolffPASTAAux


lemma pois_term_succ (r : ℝ) (n : ℕ) :
    Real.exp (-r) * r ^ (n + 1) / ((n + 1)! : ℝ) * ((n + 1 : ℕ) : ℝ)
      = r * (Real.exp (-r) * r ^ n / (n ! : ℝ)) := by
  rw [Nat.factorial_succ]
  push_cast
  have : (n ! : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma hasSum_pois_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n ! : ℝ) * (n : ℝ)) (r : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h
  refine h.congr_fun (fun n => ?_)
  exact pois_term_succ r n

lemma hasSum_pois_sq (r : ℝ≥0) :
    HasSum (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ n / (n ! : ℝ) * (n : ℝ) ^ 2)
      ((r : ℝ) + (r : ℝ) ^ 2) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := ((hasSum_pois_mean r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have key : (fun n : ℕ => Real.exp (-(r:ℝ)) * (r:ℝ) ^ (n + 1) / ((n + 1) ! : ℝ)
      * (((n + 1 : ℕ) : ℝ)) ^ 2) = fun i : ℕ => (r:ℝ) * (Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ)
        * (i : ℝ) + Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ)) := by
    funext n
    have e := pois_term_succ (r:ℝ) n
    rw [pow_two, ← mul_assoc, e]
    push_cast
    ring
  have hv : (r:ℝ) + (r:ℝ) ^ 2 - ∑ i ∈ Finset.range 1,
      Real.exp (-(r:ℝ)) * (r:ℝ) ^ i / (i ! : ℝ) * (i : ℝ) ^ 2 = (r:ℝ) * ((r:ℝ) + 1) := by
    simp; ring
  rw [hv, key]
  exact h


lemma pois_integral_id (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) ∧
      ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs] using (hasSum_pois_mean r).summable
  · rw [integral_poissonMeasure]
    simpa [smul_eq_mul] using (hasSum_pois_mean r).tsum_eq

lemma pois_integral_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) ∧
      ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = r + (r : ℝ) ^ 2 := by
  constructor
  · rw [integrable_poissonMeasure_iff]
    simpa [Real.norm_eq_abs] using (hasSum_pois_sq r).summable
  · rw [integral_poissonMeasure]
    simpa [smul_eq_mul] using (hasSum_pois_sq r).tsum_eq

end WolffPASTAAux

open WolffPASTA.Main WolffPASTAAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam) :
    ∀ᵐ ω ∂P, Tendsto (fun t => (A t ω : ℝ) / t) atTop (𝓝 lam) := by
  have hP : IsPoissonProcessWithIntensity P A (fun _ => lam) := hA
  -- increments over unit intervals
  set D : ℕ → Ω → ℕ := fun i ω => A ((i : ℝ) + 1) ω - A (i : ℝ) ω with hD
  have hDm : ∀ i, Measurable (D i) := fun i =>
    (hP.meas _).sub (hP.meas _)
  have hlaw : ∀ i, P.map (D i) = poissonMeasure lam.toNNReal := by
    intro i
    have := hP.law (i : ℝ) ((i : ℝ) + 1) (by positivity) (by linarith)
    simpa [intervalIntegral.integral_const] using this
  set X : ℕ → Ω → ℝ := fun i ω => (D i ω : ℝ) with hX
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_from_nat.comp (hDm i)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := by
    intro i
    have hDi : IdentDistrib (D i) (D 0) P P :=
      ⟨(hDm i).aemeasurable, (hDm 0).aemeasurable, by rw [hlaw, hlaw]⟩
    exact hDi.comp measurable_from_nat
  have hint : Integrable (X 0) P := by
    have h1 := (pois_integral_id lam.toNNReal).1
    rw [← hlaw 0] at h1
    exact (integrable_map_measure h1.aestronglyMeasurable (hDm 0).aemeasurable).mp h1
  have hmean : ∫ ω, X 0 ω ∂P = lam := by
    have h1 := (pois_integral_id lam.toNNReal).2
    rw [← hlaw 0, integral_map (hDm 0).aemeasurable
      (measurable_from_nat (f := fun n : ℕ => (n:ℝ))).aestronglyMeasurable] at h1
    rw [show ∫ ω, X 0 ω ∂P = ∫ ω, (D 0 ω : ℝ) ∂P from rfl, h1]
    exact Real.coe_toNNReal _ hlam.le
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) X) := by
    intro i j hij
    set k := max i j + 1 with hk
    have hI := hP.indep k (fun m : Fin (k + 1) => ((m : ℕ) : ℝ)) (by simp)
      (fun a b hab => by simpa using hab)
    have hi : i < k := by omega
    have hj : j < k := by omega
    have hne : (⟨i, hi⟩ : Fin k) ≠ ⟨j, hj⟩ := fun h => hij (by simpa using h)
    have h2 := hI.indepFun hne
    simp only [Fin.val_succ, Fin.coe_castSucc, Nat.cast_add, Nat.cast_one] at h2
    exact h2.comp measurable_from_nat measurable_from_nat
  have hslln := strong_law_ae_real X hint hindep hident
  rw [hmean] at hslln
  filter_upwards [hslln] with ω hω
  -- telescoping: ∑_{i<n} X i = A n
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, X i ω = (A (n : ℝ) ω : ℝ) := by
    intro n
    induction n with
    | zero => simp [hP.zero ω]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hmono : A (n : ℝ) ω ≤ A ((n : ℝ) + 1) ω := hP.mono ω (by linarith)
      simp only [hX, hD]
      push_cast
      rw [Nat.cast_sub hmono]
      ring
  have hseq : Tendsto (fun n : ℕ => (A (n : ℝ) ω : ℝ) / n) atTop (𝓝 lam) :=
    hω.congr (fun n => by rw [htel])
  -- upper and lower sequences
  have hup : Tendsto (fun n : ℕ => (A ((n : ℝ) + 1) ω : ℝ) / n) atTop (𝓝 lam) := by
    have h1 := (hseq.comp (tendsto_add_atTop_nat 1))
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    have := h1.mul h2
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [Function.comp, Nat.cast_add, Nat.cast_one]
    field_simp
  have hlow : Tendsto (fun n : ℕ => (A (n : ℝ) ω : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 lam) := by
    have := hseq.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hfl : Tendsto (fun t : ℝ => ⌊t⌋₊) atTop atTop := tendsto_nat_floor_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hfl) (hup.comp hfl) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hn2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have hm : (A (⌊t⌋₊ : ℝ) ω : ℝ) ≤ A t ω := by exact_mod_cast hP.mono ω hn1
    simp only [Function.comp]
    rw [div_le_div_iff₀ (by positivity) ht0]
    have := Nat.cast_nonneg (α := ℝ) (A (⌊t⌋₊ : ℝ) ω)
    nlinarith
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hn1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hn2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
    have hnpos : (1:ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.le_floor (by simpa using ht)
    have hm : (A t ω : ℝ) ≤ A ((⌊t⌋₊ : ℝ) + 1) ω := by exact_mod_cast hP.mono ω hn2.le
    simp only [Function.comp]
    rw [div_le_div_iff₀ ht0 (by linarith)]
    have := Nat.cast_nonneg (α := ℝ) (A t ω)
    nlinarith
