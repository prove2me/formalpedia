-- Prove2me | solution 1 for StrictCompatLB.Inhomogeneous.random_inhomogeneous_sparse_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:55:24.431902+00:00
-- url     : https://prove2.me/submissions/3c17c761-65a7-4ce3-b913-86089c9d4539

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_GraphConditions
import Definitions.Def_StrictCompatLB_Inhomogeneous_RandomGraph
import Theorems.Thm_StrictCompatLB_Inhomogeneous_lemma_B1
import Theorems.Thm_StrictCompatLB_Inhomogeneous_lemma_B2

open MeasureTheory Filter Topology

open StrictCompatLB.Inhomogeneous in
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (p : (N : ℕ) → Fin (M N) → ℝ) (hp_pos : ∀ N w, 0 < p N w) (hp_le : ∀ N w, p N w ≤ 1)
    (h1 : Tendsto (fun N : ℕ =>
      (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N) atTop atTop)
    (h2 : Tendsto (fun N : ℕ => (M N : ℝ) * minEdgeProb M p N) atTop atTop)
    (h3 : Tendsto (fun N : ℕ =>
      Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (N : ℕ) → Ω → (Fin N × Fin (M N) → Bool))
    (hX_meas : ∀ N, Measurable (X N)) (hX_law : ∀ N, P.map (X N) = edgeLaw M p N) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (fun N => graphOf (X N ω)) ∧
      StrictCompatLB.MeanField.IsSubcritical d M (fun N => graphOf (X N ω)) := by
  -- positivity of the minimum edge probability
  have hmin_pos : ∀ N, 0 < minEdgeProb M p N := by
    intro N
    have : Nonempty (Fin (M N)) := ⟨⟨0, hM N⟩⟩
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun w : Fin (M N) => p N w)
    unfold minEdgeProb
    rw [← hi]
    exact hp_pos N i
  -- hypothesis of Lemma B.1 : N p̄(N) → ∞
  have hN : Tendsto (fun N : ℕ => (N : ℝ) * minEdgeProb M p N) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop 3] with N hN3
    have hlogM : 0 ≤ Real.log (M N) := Real.log_nonneg (by exact_mod_cast hM N)
    have hlogN : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      apply Real.log_le_log (Real.exp_pos 1)
      have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
      linarith [Real.exp_one_lt_d9]
    have hL : 1 ≤ Real.log (M N) + Real.log N := by linarith
    have hNp : 0 ≤ (N : ℝ) * minEdgeProb M p N := by
      have := hmin_pos N; positivity
    calc (N : ℝ) / (Real.log (M N) + Real.log N) * minEdgeProb M p N
        = ((N : ℝ) * minEdgeProb M p N) / (Real.log (M N) + Real.log N) := by ring
      _ ≤ (N : ℝ) * minEdgeProb M p N := div_le_self hNp hL
  -- hypotheses of Lemma B.2
  have h_min : Tendsto (fun N : ℕ =>
      minEdgeProb M p N / ((Real.log (M N) + Real.log N) / (N : ℝ))) atTop atTop := by
    refine h1.congr (fun N => ?_)
    rw [div_div_eq_mul_div]
    ring
  have h_norm : Tendsto (fun N : ℕ =>
      invNormSq M p N / (Real.log N / (M N : ℝ) ^ 2)) atTop atTop := by
    have hpos : ∀ᶠ N : ℕ in atTop,
        0 < Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2 := by
      filter_upwards [eventually_ge_atTop 2] with N hN2
      have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
      have hMpos : (0 : ℝ) < M N := by exact_mod_cast hM N
      have hS : 0 < ∑ w : Fin (M N), 1 / (p N w) ^ 2 := by
        have : Nonempty (Fin (M N)) := ⟨⟨0, hM N⟩⟩
        apply Finset.sum_pos (fun w _ => by have := hp_pos N w; positivity) Finset.univ_nonempty
      positivity
    have h3' : Tendsto (fun N : ℕ =>
        Real.log N / (M N : ℝ) ^ 2 * ∑ w : Fin (M N), 1 / (p N w) ^ 2) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨h3, hpos⟩
    refine h3'.inv_tendsto_nhdsGT_zero.congr (fun N => ?_)
    simp only [Pi.inv_apply, invNormSq, one_div, inv_pow]
    rw [div_eq_mul_inv, mul_inv, mul_comm, div_eq_mul_inv]
  have hB1 := lemma_B1 M hM p hp_pos hp_le hN h2 P X hX_meas hX_law
  have hB2 := lemma_B2 d hd M hM p hp_pos hp_le h_min h_norm P X hX_meas hX_law
  filter_upwards [hB1, hB2] with ω h1ω h2ω
  exact ⟨h1ω, h2ω⟩
