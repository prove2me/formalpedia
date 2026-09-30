-- Prove2me | solution 1 for TraceEstimation.Rayleigh.rank_mul_lambdaMax_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:01:39.635884+00:00
-- url     : https://prove2.me/submissions/b1903d9c-58dd-46b7-9d34-ca237b253715

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic
import Definitions.Def_TraceEstimation_Rayleigh_kappaF
open Matrix TraceEstimation.Rayleigh
open scoped BigOperators
noncomputable section

private theorem spectral_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    0 < (A.rank : ℝ) ∧ (∀ i, hA.isHermitian.eigenvalues i ≤ lambdaMax hA.isHermitian) ∧
      (A.rank : ℝ) * lambdaMax hA.isHermitian ≤ A.trace * kappaF hA.isHermitian := by
  classical
  let e := hA.isHermitian.eigenvalues
  let s : Finset (Fin n) := Finset.univ.filter (fun i => e i ≠ 0)
  let N := nonzeroEigenvalues hA.isHermitian
  have hene : hA.isHermitian.eigenvalues ≠ 0 := fun h => hA0 (hA.isHermitian.eigenvalues_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hene
  change e i ≠ 0 at hi
  have hsi : i ∈ s := by simp [s, hi]
  have hne : s.Nonempty := ⟨i, hsi⟩
  have hcard : A.rank = s.card := by
    rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hrank : 0 < (A.rank : ℝ) := Nat.cast_pos.mpr (by rw [hcard]; exact hne.card_pos)
  have hmem (j : Fin n) (hj : e j ≠ 0) : e j ∈ N := by
    exact Finset.mem_image.mpr ⟨j, by simpa [e] using hj, rfl⟩
  have hN : N.Nonempty := ⟨e i, hmem i hi⟩
  have hNpos (l : ℝ) (hl : l ∈ N) : 0 < l := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
    have hj' : e j ≠ 0 := by simpa [e] using hj
    exact lt_of_le_of_ne (hA.eigenvalues_nonneg j) (Ne.symm hj')
  have hm : 0 < N.min' hN := hNpos _ (Finset.min'_mem _ _)
  have hM : 0 < N.max' hN := hNpos _ (Finset.max'_mem _ _)
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ _⟩
  have hupper (j : Fin n) : e j ≤ lambdaMax hA.isHermitian := by
    rw [lambdaMax, dif_pos hu]
    exact Finset.le_sup' _ (Finset.mem_univ j)
  have hmax : lambdaMax hA.isHermitian = N.max' hN := by
    apply le_antisymm
    · rw [lambdaMax, dif_pos hu]
      apply Finset.sup'_le
      intro j hj
      by_cases hje : e j = 0
      · change e j ≤ N.max' hN
        rw [hje]
        exact hM.le
      · exact Finset.le_max' _ _ (hmem j hje)
    · apply Finset.max'_le
      intro l hl
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
      exact hupper j
  have hsum : (∑ j ∈ s, e j) = ∑ j, e j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hj'
    simpa [s] using hj'
  have hminsum : (A.rank : ℝ) * N.min' hN ≤ A.trace := by
    calc
      _ = ∑ j ∈ s, N.min' hN := by simp [hcard]
      _ ≤ ∑ j ∈ s, e j := by
        apply Finset.sum_le_sum
        intro j hj
        have hje : e j ≠ 0 := by simpa [s] using hj
        exact Finset.min'_le _ _ (hmem j hje)
      _ = A.trace := by rw [hsum, hA.isHermitian.trace_eq_sum_eigenvalues]; rfl
  refine ⟨hrank, hupper, ?_⟩
  rw [hmax, kappaF, dif_pos hN]
  change (A.rank : ℝ) * N.max' hN ≤ A.trace * (N.max' hN / N.min' hN)
  rw [← mul_div_assoc, le_div_iff₀ hm]
  have hh := mul_le_mul_of_nonneg_right hminsum hM.le
  nlinarith

theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    (A.rank : ℝ) * lambdaMax hA.isHermitian ≤ A.trace * kappaF hA.isHermitian := by
  exact (spectral_bounds A hA hA0).2.2
