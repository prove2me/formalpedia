-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_surjective_of_card_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T06:04:44.819574+00:00
-- url     : https://prove2.me/submissions/840e2a58-7e9d-4603-9af0-a032e52c447a

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
import Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_exists_dot_offdiag_le
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
















theorem _root_.solution {k : ℕ} (A : Finset (Fin k → F))
    (hlarge : (Fintype.card F - 1) ^ 2 < A.card) :
    ∃ v : Fin k → F, A.image (fun x => dot x v) = Finset.univ := by
  classical
  obtain ⟨v, hoff⟩ := exists_dot_offdiag_le A
  refine ⟨v, ?_⟩
  by_contra hsurj
  let q := Fintype.card F
  let N := A.card
  let O := ((A.product A).filter fun xy =>
    xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v).card
  let E := ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v).card
  let c : F → ℕ := fun y => (A.filter fun x => dot x v = y).card
  let support : Finset F := Finset.univ.filter fun y => c y ≠ 0
  have hYeq : support = A.image (fun x => dot x v) := by
    ext y
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, c]
    exact Finset.fiber_card_ne_zero_iff_mem_image A (fun x => dot x v) y
  have hYcard : support.card ≤ q - 1 := by
    have hproper : support ⊂ (Finset.univ : Finset F) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro hYu
      apply hsurj
      rw [← hYeq, hYu]
    have hlt := Finset.card_lt_card hproper
    have : support.card ≤ Fintype.card F - 1 := by
      have hlt' : support.card < Fintype.card F := by
        simpa only [Finset.card_univ] using hlt
      omega
    simpa only [q] using this
  have hsumc : ∑ y ∈ support, c y = N := by
    have hall : ∑ y : F, c y = A.card := by
      symm
      simpa only [c] using (Finset.card_eq_sum_card_fiberwise
        (s := A) (t := (Finset.univ : Finset F)) (f := fun x => dot x v)
        (fun _ _ => Finset.mem_univ _))
    change ∑ y ∈ support, c y = A.card
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    exact hyY
  have hsumsq : ∑ y ∈ support, c y ^ 2 = E := by
    have hall : ∑ y : F, c y ^ 2 = E := by
      simp only [c, E, Finset.card_filter]
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp
      rw [Finset.card_filter, Finset.sum_product_right]
      simp_rw [Finset.card_filter]
    rw [← hall]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hyY
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hyY
    simp [hyY]
  have hE : E = N + O := by
    simp only [E, N, O]
    rw [show ((A.product A).filter fun xy => dot xy.1 v = dot xy.2 v) =
        A.diag ∪ ((A.product A).filter fun xy =>
          xy.1 ≠ xy.2 ∧ dot xy.1 v = dot xy.2 v) by
      ext xy
      rcases xy with ⟨x, y⟩
      by_cases hxy : x = y <;> simp [hxy]]
    rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hdiag hoffdiag
      simp only [Finset.mem_diag] at hdiag
      simp only [Finset.mem_filter] at hoffdiag
      exact hoffdiag.2.1 hdiag.2
  have hlower : N ^ 2 ≤ (q - 1) * E := by
    have hcauchy := sq_sum_le_card_mul_sum_sq (s := support) (f := c)
    rw [hsumc, hsumsq] at hcauchy
    exact hcauchy.trans (Nat.mul_le_mul_right E hYcard)
  have hupper : q * O ≤ N * (N - 1) := by
    simpa only [q, N, O] using hoff
  rw [hE] at hlower
  have hq : 1 ≤ q := by
    have : 0 < Fintype.card F := Fintype.card_pos
    simp only [q]
    omega
  have hNpos : 0 < N := by
    have : 0 < (q - 1) ^ 2 + 1 := by omega
    have := hlarge
    simp only [N] at this ⊢
    omega
  have hN : 1 ≤ N := hNpos
  have hlowerZ0 : (N : ℤ) ^ 2 ≤ ((q - 1 : ℕ) : ℤ) * ((N : ℤ) + (O : ℤ)) := by
    exact_mod_cast hlower
  have hlowerZ : (N : ℤ) ^ 2 ≤ ((q : ℤ) - 1) * ((N : ℤ) + (O : ℤ)) := by
    simpa only [Nat.cast_sub hq, Nat.cast_one] using hlowerZ0
  have hupperZ0 : (q : ℤ) * (O : ℤ) ≤ (N : ℤ) * ((N - 1 : ℕ) : ℤ) := by
    exact_mod_cast hupper
  have hupperZ : (q : ℤ) * (O : ℤ) ≤ (N : ℤ) * ((N : ℤ) - 1) := by
    simpa only [Nat.cast_sub hN, Nat.cast_one] using hupperZ0
  have hlargeZ0 : (((q - 1 : ℕ) : ℤ) ^ 2) < (N : ℤ) := by
    exact_mod_cast (show (q - 1) ^ 2 < N by simpa only [q, N] using hlarge)
  have hlargeZ : ((q : ℤ) - 1) ^ 2 < (N : ℤ) := by
    simpa only [Nat.cast_sub hq, Nat.cast_one] using hlargeZ0
  have hqZ : 0 ≤ (q : ℤ) := by omega
  have hqZone : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hqm1Z : 0 ≤ (q : ℤ) - 1 := by omega
  have hlowerScaled := mul_le_mul_of_nonneg_left hlowerZ hqZ
  have hupperScaled := mul_le_mul_of_nonneg_left hupperZ hqm1Z
  have hNZ : 0 < (N : ℤ) := by exact_mod_cast hNpos
  nlinarith
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
