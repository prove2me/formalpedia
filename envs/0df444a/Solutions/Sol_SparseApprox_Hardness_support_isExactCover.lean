-- Prove2me | solution 1 for SparseApprox.Hardness.support_isExactCover
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:09:46.494921+00:00
-- url     : https://prove2.me/submissions/60826dc7-2e44-46ad-ad96-ba5bf310af35

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

open SparseApprox.Hardness
open Matrix

theorem solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖Matrix.toEuclideanLin (incidence C) x - onesVec m‖ ≤ 1 / 2)
    (hsparse : 3 * nnz x ≤ m) :
    IsExactCover C (Finset.univ.filter (fun j => x j ≠ 0)) := by
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
  choose g hgx hgmem using hex
  let S : Finset (Fin n) := Finset.univ.filter (fun j => x j ≠ 0)
  let fib : Fin n → Finset (Fin m) := fun j => Finset.univ.filter (fun i => g i = j)
  have hSnnz : S.card = nnz x := rfl
  have hcard : m = ∑ j ∈ S, (fib j).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin m))) (t := S)
      (f := g) (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgx i⟩)
    simpa [fib] using h
  have hfib_sub : ∀ j, fib j ⊆ C j := by
    intro j i hi
    have hgij : g i = j := (Finset.mem_filter.mp hi).2
    rw [← hgij]
    exact hgmem i
  have hterm : ∀ j ∈ S, (fib j).card = 3 := by
    have hle : ∀ j ∈ S, (fib j).card ≤ 3 := by
      intro j _
      calc (fib j).card ≤ (C j).card := Finset.card_le_card (hfib_sub j)
        _ = 3 := hC j
    have hsum_le : ∑ j ∈ S, (fib j).card ≤ ∑ j ∈ S, 3 := Finset.sum_le_sum hle
    have hsum_ge : (∑ j ∈ S, 3) ≤ ∑ j ∈ S, (fib j).card := by
      have h3 : (∑ j ∈ S, 3) = 3 * S.card := by
        rw [Finset.sum_const]
        simp [smul_eq_mul]
        omega
      calc ∑ j ∈ S, 3 = 3 * S.card := h3
        _ = 3 * nnz x := by rw [hSnnz]
        _ ≤ m := hsparse
        _ = ∑ j ∈ S, (fib j).card := hcard
    exact (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm hsum_le hsum_ge)
  have hfib_eq : ∀ j ∈ S, fib j = C j := by
    intro j hjS
    exact Finset.eq_of_subset_of_card_le (hfib_sub j) (by rw [hC j, hterm j hjS])
  intro i
  refine ⟨g i, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgx i⟩, hgmem i⟩, ?_⟩
  rintro j ⟨hjS, hji⟩
  have hmemi : i ∈ fib j := by
    rw [hfib_eq j hjS]
    exact hji
  exact ((Finset.mem_filter.mp hmemi).2).symm
