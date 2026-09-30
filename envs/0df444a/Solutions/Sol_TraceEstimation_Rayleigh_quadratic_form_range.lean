-- Prove2me | solution 1 for TraceEstimation.Rayleigh.quadratic_form_range
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:04:13.093012+00:00
-- url     : https://prove2.me/submissions/14db1c75-c71d-4c83-84b0-91d4e632b812

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

open scoped RealInnerProductSpace
private theorem rayleigh_upper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hA0 : A ≠ 0) (z : Fin n → ℝ) :
    z ⬝ᵥ (A *ᵥ z) ≤ lambdaMax hA.isHermitian * (z ⬝ᵥ z) := by
  classical
  let v := hA.isHermitian.eigenvectorBasis
  let e := hA.isHermitian.eigenvalues
  let L := A.toEuclideanLin
  let s : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 z
  have hL : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have hev (i : Fin n) : L (v i) = e i • v i := by
    apply WithLp.ofLp_injective
    change A *ᵥ (v i).ofLp = e i • (v i).ofLp
    exact hA.isHermitian.mulVec_eigenvectorBasis i
  have hi (i : Fin n) : ⟪v i, L s⟫ = e i * ⟪v i, s⟫ := by
    rw [← hL, hev, real_inner_smul_left]
  have hid : ⟪L s, s⟫ = ∑ i, e i * ⟪v i, s⟫^2 := by
    rw [← v.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (v i) (L s), hi]
    ring
  have hu : ⟪L s, s⟫ ≤ lambdaMax hA.isHermitian * ‖s‖^2 := by
    rw [hid, ← v.sum_sq_inner_right, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right ((spectral_bounds A hA hA0).2.1 i) (sq_nonneg _)
  have hn : ‖s‖^2 = z ⬝ᵥ z := by
    rw [← real_inner_self_eq_norm_sq]
    change z ⬝ᵥ star z = z ⬝ᵥ z
    simp
  rw [hn] at hu
  simpa [EuclideanSpace.inner_eq_star_dotProduct,
    L, s, Matrix.ofLp_toEuclideanLin_apply, dotProduct_comm] using hu

theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hA0 : A ≠ 0) (z : Fin n → ℝ) (hz : z ⬝ᵥ z = (n : ℝ)) :
    0 ≤ z ⬝ᵥ (A *ᵥ z) ∧
      z ⬝ᵥ (A *ᵥ z) ≤ lambdaMax hA.isHermitian * (z ⬝ᵥ z) ∧
      lambdaMax hA.isHermitian * (z ⬝ᵥ z) = (n : ℝ) * lambdaMax hA.isHermitian ∧
      (n : ℝ) * lambdaMax hA.isHermitian ≤
        (n : ℝ) / (A.rank : ℝ) * A.trace * kappaF hA.isHermitian := by
  refine ⟨?_, rayleigh_upper A hA hA0 z, ?_, ?_⟩
  · simpa using hA.dotProduct_mulVec_nonneg z
  · rw [hz, mul_comm]
  · have hb := spectral_bounds A hA hA0
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have h := mul_le_mul_of_nonneg_left hb.2.2 (div_nonneg hn hb.1.le)
    have hcancel : (n : ℝ) / (A.rank : ℝ) * ((A.rank : ℝ) * lambdaMax hA.isHermitian) =
        (n : ℝ) * lambdaMax hA.isHermitian := by field_simp [ne_of_gt hb.1]
    rw [hcancel] at h
    simpa only [mul_assoc] using h
