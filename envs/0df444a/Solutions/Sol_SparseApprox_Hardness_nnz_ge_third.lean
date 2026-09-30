-- Prove2me | solution 1 for SparseApprox.Hardness.nnz_ge_third
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:06:58.721546+00:00
-- url     : https://prove2.me/submissions/92f63157-00da-4d17-9301-d40c71f70e14

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

open SparseApprox.Hardness
open Matrix

theorem solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2) :
    m ≤ 3 * nnz x := by
  have hcoord_eq : ∀ i, (Matrix.toEuclideanLin (incidence C) x) i
      = ∑ j, incidence C i j * x j := by
    intro i
    change (Matrix.toEuclideanLin (incidence C) x).ofLp i
      = ∑ j, incidence C i j * x.ofLp j
    rw [show (Matrix.toEuclideanLin (incidence C) x).ofLp = incidence C *ᵥ x.ofLp from rfl]
    rw [Matrix.mulVec]
    rfl
  have hhalf : ∀ i, 1 / 2 ≤ (Matrix.toEuclideanLin (incidence C) x) i := by
    intro i
    have hc : ‖(Matrix.toEuclideanLin (incidence C) x - onesVec m) i‖ ≤ 1 / 2 :=
      (PiLp.norm_apply_le _ i).trans hx
    have hone : (onesVec m) i = 1 := rfl
    rw [PiLp.sub_apply, hone, Real.norm_eq_abs] at hc
    linarith [abs_le.mp hc]
  have hex : ∀ i, ∃ j, x j ≠ 0 ∧ i ∈ C j := by
    intro i
    by_contra h
    push_neg at h
    have hzero : (Matrix.toEuclideanLin (incidence C) x) i = 0 := by
      rw [hcoord_eq i]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hxj : x j = 0
      · simp [hxj]
      · have hij : i ∉ C j := h j hxj
        simp [incidence, hij]
    have := hhalf i
    linarith
  let S : Finset (Fin n) := Finset.univ.filter (fun j => x j ≠ 0)
  have hS : S.card = nnz x := rfl
  choose g hgx hgmem using hex
  have hcover : (Finset.univ : Finset (Fin m)) ⊆ S.biUnion C := by
    intro i _
    rw [Finset.mem_biUnion]
    exact ⟨g i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgx i⟩, hgmem i⟩
  have hsum : (∑ j ∈ S, (C j).card) = 3 * S.card := by
    calc ∑ j ∈ S, (C j).card = ∑ j ∈ S, 3 := by
          apply Finset.sum_congr rfl
          intro j _
          exact hC j
      _ = S.card * 3 := by
          rw [Finset.sum_const]
          simp [smul_eq_mul]
      _ = 3 * S.card := by ring
  calc m = (Finset.univ : Finset (Fin m)).card := by simp
    _ ≤ (S.biUnion C).card := Finset.card_le_card hcover
    _ ≤ ∑ j ∈ S, (C j).card := Finset.card_biUnion_le
    _ = 3 * S.card := hsum
    _ = 3 * nnz x := by rw [hS]
