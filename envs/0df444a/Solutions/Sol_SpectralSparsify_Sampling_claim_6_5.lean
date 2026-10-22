-- Prove2me | solution 1 for SpectralSparsify.Sampling.claim_6_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:06:18.97496+00:00
-- url     : https://prove2.me/submissions/09ba700c-349f-4f99-8299-0a63dba90b2e

import Mathlib
import Definitions.Def_SpectralSparsify_Sampling_BernoulliSubset
import Definitions.Def_SpectralSparsify_Sampling_EdgeSampling

set_option autoImplicit false
open SpectralSparsify.Sampling

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, 0 < G.degree v) (Υ : ℝ) (hΥ : 1 < Υ)
    (T : Finset (Sym2 V)) (hT : T ⊆ G.edgeFinset)
    (hTpos : 0 < outcomeProb G.edgeFinset (degSampleProb G Υ) T) (i j : V) :
    |deltaMat G (degSampleProb G Υ) T i j| ≤ 1 / Υ := by
  have hΥ0 : 0 < Υ := by linarith
  have hd : ∀ v, (0 : ℝ) < (G.degree v : ℝ) := fun v => by exact_mod_cast hdeg v
  have hp : ∀ a b : V, degSampleProb G Υ s(a, b) =
      min 1 (Υ / min (G.degree a : ℝ) (G.degree b : ℝ)) := fun a b => rfl
  have hinv : 0 ≤ 1 / Υ := by positivity
  unfold deltaMat
  rw [Matrix.diagonal_mul]
  simp only [Matrix.sub_apply, adjMat, Matrix.of_apply, sampledWeight,
    SimpleGraph.adjMatrix_apply]
  by_cases hadj : G.Adj i j
  · have hmem : s(i, j) ∈ G.edgeFinset := by simpa using hadj
    have hm : (0 : ℝ) < min (G.degree i : ℝ) (G.degree j : ℝ) := lt_min (hd i) (hd j)
    have hmi : min (G.degree i : ℝ) (G.degree j : ℝ) ≤ G.degree i := min_le_left _ _
    have hdi := hd i
    by_cases hin : s(i, j) ∈ T
    · simp only [hin, hadj, if_true]
      rw [hp]
      by_cases h1 : Υ / min (G.degree i : ℝ) (G.degree j : ℝ) < 1
      · rw [min_eq_right h1.le]
        have e : 1 / (Υ / min (G.degree i : ℝ) (G.degree j : ℝ)) =
            min (G.degree i : ℝ) (G.degree j : ℝ) / Υ := by field_simp
        rw [e]
        have hgt : 1 ≤ min (G.degree i : ℝ) (G.degree j : ℝ) / Υ := by
          rw [le_div_iff₀ hΥ0]
          rw [div_lt_one hm] at h1
          linarith
        have hA : 0 ≤ min (G.degree i : ℝ) (G.degree j : ℝ) / Υ - 1 := by linarith
        have hB : min (G.degree i : ℝ) (G.degree j : ℝ) / Υ ≤ (G.degree i : ℝ) / Υ := by
          gcongr
        rw [abs_of_nonneg (mul_nonneg (by positivity) hA)]
        calc 1 / (G.degree i : ℝ) * (min (G.degree i : ℝ) (G.degree j : ℝ) / Υ - 1)
            ≤ 1 / (G.degree i : ℝ) * ((G.degree i : ℝ) / Υ) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = 1 / Υ := by field_simp
      · push_neg at h1
        rw [min_eq_left h1]
        simp [hinv, hΥ0.le]
    · simp only [hin, hadj, if_true, if_false]
      -- positivity of the outcome forces p < 1 on dropped edges
      have hne : (1 - degSampleProb G Υ s(i, j)) ≠ 0 := by
        have h0 : (∏ e ∈ G.edgeFinset \ T, (1 - degSampleProb G Υ e)) ≠ 0 := by
          intro h
          unfold outcomeProb at hTpos
          rw [h, mul_zero] at hTpos
          exact lt_irrefl _ hTpos
        rw [Finset.prod_ne_zero_iff] at h0
        exact h0 _ (Finset.mem_sdiff.mpr ⟨hmem, hin⟩)
      rw [hp] at hne
      have h1 : Υ / min (G.degree i : ℝ) (G.degree j : ℝ) < 1 := by
        by_contra hcon
        push_neg at hcon
        apply hne
        rw [min_eq_left hcon]
        ring
      rw [div_lt_one hm] at h1
      have : |1 / (G.degree i : ℝ) * (0 - 1)| = 1 / (G.degree i : ℝ) := by
        rw [mul_sub, mul_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
        ring
      rw [this]
      rw [div_le_div_iff₀ hdi hΥ0]
      linarith
  · have hnot : s(i, j) ∉ T := fun h => hadj (by simpa using hT h)
    simp [hnot, hadj, hinv, hΥ0.le]
