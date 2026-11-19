-- Prove2me | solution 1 for PathORAMCap.lemma_4_14
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T08:00:57.489317+00:00
-- url     : https://prove2.me/submissions/1945c5b6-9c9d-4dc6-bf70-2f482f374d0c

import Mathlib
import Definitions.Def_PathORAMCap_IsIncrDirConvex

open MeasureTheory ProbabilityTheory Finset PathORAMCap
open scoped ENNReal NNReal

lemma incr_tel {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : IsIncrDirConvex f) (z : Fin d → ℝ) (hz : 0 ≤ z) :
    ∀ N : ℕ, ∀ c : Fin d → ℕ, ∑ i, c i = N →
      ∑ i, (c i : ℝ) * (f (z + Pi.single i 1) - f z) ≤ f (z + fun i => (c i : ℝ)) - f z := by
  intro N
  induction N with
  | zero =>
    intro c hc
    have h0 : ∀ i, c i = 0 := fun i => (sum_eq_zero_iff.mp hc) i (mem_univ i)
    have hz0 : (z + fun i => (c i : ℝ)) = z := by funext i; simp [h0]
    rw [hz0]; simp [h0]
  | succ N ih =>
    intro c hc
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra h; push Not at h; simp [h] at hc
    set c' := Function.update c j (c j - 1) with hc'
    have hcc : ∀ i, (c i : ℝ) = (c' i : ℝ) + (Pi.single j (1 : ℝ) : Fin d → ℝ) i := by
      intro i
      by_cases hij : i = j
      · subst hij; simp [hc']; rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj)]; ring
      · simp [hc', hij]
    have hsum' : ∑ i, c' i = N := by
      have : ∑ i, c i = ∑ i, c' i + 1 := by
        have h2 : ∀ i, c i = c' i + (Pi.single j (1 : ℕ) : Fin d → ℕ) i := by
          intro i
          by_cases hij : i = j
          · subst hij; simp [hc']; omega
          · simp [hc', hij]
        rw [sum_congr rfl (fun i _ => h2 i), sum_add_distrib]
        simp
      omega
    have ih' := ih c' hsum'
    have hvec : (fun i => (c i : ℝ)) = (fun i => (c' i : ℝ)) + (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
      funext i; simp only [Pi.add_apply]; exact hcc i
    have hc'0 : (0 : Fin d → ℝ) ≤ fun i => (c' i : ℝ) := fun i => by positivity
    have hej : (0 : Fin d → ℝ) ≤ (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
      intro i; by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hdc := hf.2 z (Pi.single j 1) (fun i => (c' i : ℝ)) hz hej hc'0
    have hsplit : ∑ i, (c i : ℝ) * (f (z + Pi.single i 1) - f z) =
        ∑ i, (c' i : ℝ) * (f (z + Pi.single i 1) - f z) + (f (z + Pi.single j 1) - f z) := by
      simp_rw [hcc, add_mul, sum_add_distrib]
      congr 1
      rw [sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsplit, hvec]
    have : z + ((fun i => (c' i : ℝ)) + (Pi.single j (1 : ℝ) : Fin d → ℝ)) =
        z + Pi.single j 1 + fun i => (c' i : ℝ) := by abel
    rw [this]
    linarith

lemma pois_mean (r : ℝ≥0) : ∑' n : ℕ, (n : ℝ≥0∞) * poissonMeasure r {n} = r := by
  simp_rw [poissonMeasure_singleton]
  have hq : ∀ n : ℕ, 0 ≤ Real.exp (-r) * r ^ n / n.factorial := fun n => by positivity
  have hs : HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-r) * r ^ n / n.factorial)) r := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    have := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
    rw [mul_one] at this
    convert this using 1
    all_goals try rfl
    funext n
    rw [Nat.factorial_succ]; push_cast
    field_simp
    ring
  have : ∀ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / n.factorial) =
      ENNReal.ofReal ((n : ℝ) * (Real.exp (-r) * r ^ n / n.factorial)) := by
    intro n; rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  simp_rw [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by have := hq n; positivity) hs.summable, hs.tsum_eq]
  simp

theorem solution (d : ℕ) (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i ≤ 1)
    (f : (Fin d → ℝ) → ℝ) (hf : IsIncrDirConvex f) :
    (∀ z : Fin d → ℝ, 0 ≤ z →
      ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f (z + Pi.single i 1) - f z) ≤
        ∑' c : Fin d → ℕ, (∏ i, poissonMeasure (p i).toNNReal {c i}) *
          ENNReal.ofReal (f (z + fun i => (c i : ℝ)) - f z)) ∧
    (Measurable f → ∀ μ : Measure (Fin d → ℝ), IsProbabilityMeasure μ → (∀ᵐ y ∂μ, 0 ≤ y) →
      ∫⁻ y, ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f (y + Pi.single i 1) - f y) ∂μ ≤
        ∫⁻ y, ∑' c : Fin d → ℕ, (∏ i, poissonMeasure (p i).toNNReal {c i}) *
          ENNReal.ofReal (f (y + fun i => (c i : ℝ)) - f y) ∂μ) := by
  have part1 : ∀ z : Fin d → ℝ, 0 ≤ z →
      ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f (z + Pi.single i 1) - f z) ≤
        ∑' c : Fin d → ℕ, (∏ i, poissonMeasure (p i).toNNReal {c i}) *
          ENNReal.ofReal (f (z + fun i => (c i : ℝ)) - f z) := by
    intro z hz
    set P : Measure (Fin d → ℕ) := Measure.pi fun i => poissonMeasure (p i).toNNReal with hP
    have hΔ : ∀ i, 0 ≤ f (z + Pi.single i 1) - f z := by
      intro i
      have hle : z ≤ z + Pi.single i 1 := by
        intro j; by_cases hij : j = i
        · subst hij; simp
        · simp [hij]
      linarith [hf.1 z _ hz hle]
    -- pointwise lower bound
    have hpt : ∀ c : Fin d → ℕ, ∑ i, (c i : ℝ≥0∞) * ENNReal.ofReal (f (z + Pi.single i 1) - f z) ≤
        ENNReal.ofReal (f (z + fun i => (c i : ℝ)) - f z) := by
      intro c
      have h := incr_tel f hf z hz _ c rfl
      calc ∑ i, (c i : ℝ≥0∞) * ENNReal.ofReal (f (z + Pi.single i 1) - f z)
          = ENNReal.ofReal (∑ i, (c i : ℝ) * (f (z + Pi.single i 1) - f z)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by positivity) (hΔ i))]
            apply sum_congr rfl; intro i _
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        _ ≤ _ := ENNReal.ofReal_le_ofReal h
    have hmean : ∀ i, ∑' c : Fin d → ℕ, (∏ j, poissonMeasure (p j).toNNReal {c j}) * (c i : ℝ≥0∞) =
        ENNReal.ofReal (p i) := by
      intro i
      have h1 : ∑' c : Fin d → ℕ, (∏ j, poissonMeasure (p j).toNNReal {c j}) * (c i : ℝ≥0∞) =
          ∫⁻ c, (c i : ℝ≥0∞) ∂P := by
        rw [lintegral_countable']
        apply tsum_congr; intro c
        rw [hP, Measure.pi_singleton, mul_comm]
      rw [h1]
      have h2 : ∫⁻ c, (c i : ℝ≥0∞) ∂P = ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure (p i).toNNReal) :=
        (measurePreserving_eval (fun j => poissonMeasure (p j).toNNReal) i).lintegral_comp
          (f := fun n : ℕ => (n : ℝ≥0∞)) measurable_from_top
      rw [h2, lintegral_countable', pois_mean]
      rfl
    calc ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (f (z + Pi.single i 1) - f z)
        = ∑ i, ∑' c : Fin d → ℕ, (∏ j, poissonMeasure (p j).toNNReal {c j}) *
            ((c i : ℝ≥0∞) * ENNReal.ofReal (f (z + Pi.single i 1) - f z)) := by
          apply sum_congr rfl; intro i _
          rw [← hmean i, ← ENNReal.tsum_mul_right]
          apply tsum_congr; intro c; ring
      _ = ∑' c : Fin d → ℕ, (∏ j, poissonMeasure (p j).toNNReal {c j}) *
            ∑ i, (c i : ℝ≥0∞) * ENNReal.ofReal (f (z + Pi.single i 1) - f z) := by
          rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
          apply tsum_congr; intro c; rw [mul_sum]
      _ ≤ _ := ENNReal.tsum_le_tsum (fun c => mul_le_mul_of_nonneg_left (hpt c) (zero_le))
  refine ⟨part1, fun _ μ _ hμ => ?_⟩
  exact lintegral_mono_ae (hμ.mono fun y hy => part1 y hy)
