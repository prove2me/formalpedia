-- Prove2me | solution 1 for SparseApprox.Hardness.exactCover_gives_exact_solution
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:09:47.326467+00:00
-- url     : https://prove2.me/submissions/c2880c31-a86c-4760-9caf-efaa7b9386f0

import Mathlib
import Definitions.Def_SparseApprox_Hardness_Basic

open SparseApprox.Hardness
open Matrix

theorem solution {m n : ℕ} (C : Fin n → Finset (Fin m))
    (hC : ∀ j, (C j).card = 3) (J : Finset (Fin n)) (hJ : IsExactCover C J) :
    Matrix.toEuclideanLin (incidence C) (indicatorVec J) = onesVec m ∧
      3 * nnz (indicatorVec J) = m := by
  classical
  have hpt : ∀ j, indicatorVec J j = (if j ∈ J then (1 : ℝ) else 0) := fun j => rfl
  have hcoord : ∀ i, (Matrix.toEuclideanLin (incidence C) (indicatorVec J)) i
      = ∑ j, incidence C i j * indicatorVec J j := by
    intro i
    rw [show (Matrix.toEuclideanLin (incidence C) (indicatorVec J)).ofLp
        = incidence C *ᵥ (indicatorVec J).ofLp from rfl]
    rw [Matrix.mulVec]
    rfl
  have hone : ∀ i, (Matrix.toEuclideanLin (incidence C) (indicatorVec J)) i = 1 := by
    intro i
    rw [hcoord i]
    obtain ⟨j0, hj0, huniq⟩ := hJ i
    rw [show (∑ j, incidence C i j * indicatorVec J j)
        = ∑ j, (if j = j0 then (1 : ℝ) else 0) from ?_]
    · rw [Fintype.sum_ite_eq']
    · apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = j0
      · subst hj
        simp [incidence, hpt, hj0.1, hj0.2]
      · by_cases hJj : j ∈ J
        · have hiCj : i ∉ C j := fun h => hj (huniq j ⟨hJj, h⟩)
          simp [incidence, hpt, hj, hJj, hiCj]
        · simp [incidence, hpt, hj, hJj]
  have hnnz : nnz (indicatorVec J) = J.card := by
    show (Finset.univ.filter (fun j => indicatorVec J j ≠ 0)).card = J.card
    congr 1
    ext j
    rw [Finset.mem_filter, hpt j]
    by_cases hJj : j ∈ J <;> simp [hJj]
  let f : Fin m → Fin n := fun i => Classical.choose (hJ i)
  have hf : ∀ i, f i ∈ J ∧ i ∈ C (f i) := fun i => (Classical.choose_spec (hJ i)).1
  have hfuniq : ∀ i (j : Fin n), j ∈ J → i ∈ C j → j = f i := by
    intro i j hjJ hji
    exact (Classical.choose_spec (hJ i)).2 j ⟨hjJ, hji⟩
  have hcover : (Finset.univ : Finset (Fin m)) = J.biUnion C := by
    apply Finset.Subset.antisymm
    · intro i _
      rw [Finset.mem_biUnion]
      exact ⟨f i, (hf i).1, (hf i).2⟩
    · intro i _
      exact Finset.mem_univ i
  have hdisj : (J : Set (Fin n)).PairwiseDisjoint C := by
    intro x hx y hy hxy
    change Disjoint (C x) (C y)
    rw [Finset.disjoint_left]
    intro i hix hiy
    exact hxy ((hfuniq i x hx hix).trans (hfuniq i y hy hiy).symm)
  have hmeq : m = ∑ j ∈ J, (C j).card := by
    calc m = (Finset.univ : Finset (Fin m)).card := by simp
      _ = (J.biUnion C).card := by rw [hcover]
      _ = ∑ j ∈ J, (C j).card := Finset.card_biUnion hdisj
  have hsum3 : (∑ j ∈ J, (C j).card) = 3 * J.card := by
    calc ∑ j ∈ J, (C j).card = ∑ j ∈ J, 3 := Finset.sum_congr rfl (fun j _ => hC j)
      _ = J.card * 3 := by
          rw [Finset.sum_const]
          simp [smul_eq_mul]
      _ = 3 * J.card := by omega
  constructor
  · ext i
    rw [hone i]
    rfl
  · rw [hnnz]
    exact (hmeq.trans hsum3).symm
