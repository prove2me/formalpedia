-- Prove2me | solution 1 for RegretMatching.Approach.exists_invariant_vector
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:11:38.221755+00:00
-- url     : https://prove2.me/submissions/12b1dae3-9851-4f7d-b1ea-66c73ba998cc

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open RegretMatching.Approach Finset

theorem solution
    {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (lam : OffDiag A → ℝ) (hlam : ∀ l, 0 ≤ lam l) :
    ∃ q ∈ stdSimplex ℝ A, ∀ j : A,
      ∑ k : A, q k * lamMat lam k j = q j * ∑ k : A, lamMat lam j k := by
  classical
  let e : A → (A → ℝ) := fun k => Pi.single k 1
  let g : A → (A → ℝ) := fun k =>
    ∑ j : A, lamMat lam k j • (e j - e k)
  have h0 : (0 : A → ℝ) ∈ convexHull ℝ (Set.range g) := by
    by_contra hn
    obtain ⟨f, b, hb, hf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) ((Set.finite_range g).isCompact_convexHull (𝕜 := ℝ)).isClosed hn
    obtain ⟨k, hk, hmax⟩ := exists_max_image (univ : Finset A) (fun j => f (e j))
      univ_nonempty
    have hg : f (g k) ≤ 0 := by
      dsimp [g]
      rw [map_sum]
      apply sum_nonpos
      intro j _
      rw [map_smul, map_sub]
      apply mul_nonpos_of_nonneg_of_nonpos
      · unfold lamMat
        split_ifs
        · rfl
        · exact hlam _
      · exact sub_nonpos.mpr (hmax j (mem_univ j))
    have hh := hf (g k) (subset_convexHull ℝ _ (Set.mem_range_self k))
    simp only [map_zero] at hb
    linarith
  rw [convexHull_range_eq_exists_affineCombination] at h0
  obtain ⟨s, a, ha, hsum, he⟩ := h0
  rw [s.affineCombination_eq_linear_combination g a hsum] at he
  let q : A → ℝ := fun k => if k ∈ s then a k else 0
  have hq : q ∈ stdSimplex ℝ A := by
    constructor
    · intro k
      dsimp [q]
      split_ifs with hk
      · exact ha k hk
      · rfl
    · simpa [q] using hsum
  refine ⟨q, hq, ?_⟩
  have hvec : ∑ k : A, q k • g k = 0 := by
    simpa [q, ite_smul] using he
  intro j
  have hj := congrFun hvec j
  have hg (k : A) : g k j = lamMat lam k j -
      (if k = j then ∑ t : A, lamMat lam k t else 0) := by
    simp [g, e, Pi.single_apply, sub_apply, sum_sub_distrib,
      smul_eq_mul, mul_sub, mul_ite, sum_ite_eq, sum_ite_eq', eq_comm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg, mul_sub, mul_ite,
    mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ, if_true, Pi.zero_apply] at hj
  exact sub_eq_zero.mp hj

#print axioms solution
