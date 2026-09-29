-- Prove2me | solution 1 for SparseApprox.Hardness.exactCover_iff_sparse_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T01:13:10.23939+00:00
-- url     : https://prove2.me/submissions/8805d76f-b5f9-438f-9383-746830385e82

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

open SparseApprox.Hardness in
theorem solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) :
    (∃ J : Finset (Fin n), IsExactCover C J) ↔
      ∃ x : EuclideanSpace ℝ (Fin n),
        ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2 ∧ 3 * nnz x ≤ m := by
  have happly : ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin m),
      (Matrix.toEuclideanLin (incidence C) x) i
        = ∑ j, (if i ∈ C j then (1:ℝ) else 0) * x j := by
    intro x i
    rw [show Matrix.toEuclideanLin (incidence C) x
        = WithLp.toLp 2 (Matrix.mulVec (incidence C) (WithLp.ofLp x)) from rfl]
    simp [Matrix.mulVec, dotProduct, incidence]
  have hdc : ∀ S : Finset (Fin n),
      ∑ i : Fin m, (S.filter (fun j => i ∈ C j)).card = 3 * S.card := by
    intro S
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ i : Fin m, (if i ∈ C j then 1 else 0) = (C j).card := by
      intro j
      rw [← Finset.card_filter]
      congr 1
      ext k
      simp
    simp [h1, hC, mul_comm]
  constructor
  · rintro ⟨J, hJ⟩
    have hcount : ∀ i, (J.filter (fun j => i ∈ C j)).card = 1 := by
      intro i
      obtain ⟨j, ⟨hjJ, hij⟩, huniq⟩ := hJ i
      rw [Finset.card_eq_one]
      refine ⟨j, ?_⟩
      ext k
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hk
        exact huniq k hk
      · rintro rfl
        exact ⟨hjJ, hij⟩
    refine ⟨indicatorVec J, ?_, ?_⟩
    · have hzero : Matrix.toEuclideanLin (incidence C) (indicatorVec J) - onesVec m = 0 := by
        ext i
        rw [PiLp.sub_apply, happly]
        have h2 : ∑ j, (if i ∈ C j then (1:ℝ) else 0) * (indicatorVec J) j
            = ((J.filter (fun j => i ∈ C j)).card : ℝ) := by
          rw [Finset.card_filter]
          push_cast
          rw [← Finset.sum_subset (Finset.subset_univ J)]
          · apply Finset.sum_congr rfl
            intro j hj
            simp [indicatorVec, hj]
          · intro j _ hj
            simp [indicatorVec, hj]
        rw [h2, hcount i]
        simp [onesVec]
      rw [hzero, norm_zero]
      norm_num
    · have hn : nnz (indicatorVec J) = J.card := by
        unfold nnz indicatorVec
        congr 1
        ext j
        simp
      rw [hn, ← hdc J]
      simp [hcount]
  · rintro ⟨x, hnorm, hnnz⟩
    set S := Finset.univ.filter (fun j => x j ≠ 0) with hS
    have hnnzS : nnz x = S.card := rfl
    have hcov : ∀ i, 1 ≤ (S.filter (fun j => i ∈ C j)).card := by
      intro i
      by_contra h
      have hempty : S.filter (fun j => i ∈ C j) = ∅ := by
        rw [← Finset.card_eq_zero]
        omega
      have hAi : (Matrix.toEuclideanLin (incidence C) x) i = 0 := by
        rw [happly]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hij : i ∈ C j
        · have hx0 : x j = 0 := by
            by_contra hx
            have hmem : j ∈ S.filter (fun j => i ∈ C j) := by
              rw [Finset.mem_filter, hS, Finset.mem_filter]
              exact ⟨⟨Finset.mem_univ _, hx⟩, hij⟩
            rw [hempty] at hmem
            simp at hmem
          simp [hx0]
        · simp [hij]
      have hcoord := PiLp.norm_apply_le
        (Matrix.toEuclideanLin (incidence C) x - onesVec m) i
      have hone : (onesVec m) i = 1 := rfl
      rw [PiLp.sub_apply, hAi, hone, zero_sub, norm_neg, norm_one] at hcoord
      linarith
    have hsum : ∑ i : Fin m, (S.filter (fun j => i ∈ C j)).card = ∑ _i : Fin m, 1 := by
      apply le_antisymm
      · rw [hdc S]
        simp
        omega
      · exact Finset.sum_le_sum (fun i _ => hcov i)
    have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hcov i)).mp hsum.symm
    refine ⟨S, fun i => ?_⟩
    have h1 : (S.filter (fun j => i ∈ C j)).card = 1 := (heq i (Finset.mem_univ _)).symm
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
    have hjmem : j ∈ S.filter (fun j => i ∈ C j) := by
      rw [hj]
      exact Finset.mem_singleton_self j
    rw [Finset.mem_filter] at hjmem
    refine ⟨j, hjmem, ?_⟩
    intro k hk
    have hkmem : k ∈ S.filter (fun j => i ∈ C j) := by
      rw [Finset.mem_filter]
      exact hk
    rw [hj] at hkmem
    exact Finset.mem_singleton.mp hkmem
