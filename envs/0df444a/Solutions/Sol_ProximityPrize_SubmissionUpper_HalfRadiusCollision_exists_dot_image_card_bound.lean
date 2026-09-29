-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.HalfRadiusCollision.exists_dot_image_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T05:54:28.51959+00:00
-- url     : https://prove2.me/submissions/58758d8f-cdfd-4e2a-9cec-aabf0d466318

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
import Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_exists_dot_offdiag_le
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]













/-- Some linear functional has an image whose density is at least
`|A| / (|F| + |A| - 1)`.  This is the quantitative form of the collision
argument: unlike `exists_dot_surjective_of_card_sq_lt`, it does not require the
image to be all of `F`. -/
theorem _root_.solution {k : ℕ} (A : Finset (Fin k → F)) :
    ∃ v : Fin k → F,
      A.card * Fintype.card F ≤
        (A.image (fun x => dot x v)).card * (Fintype.card F + A.card - 1) := by
  classical
  by_cases hA : A.card = 0
  · refine ⟨0, ?_⟩
    simp [hA]
  obtain ⟨v, hoff⟩ := exists_dot_offdiag_le A
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
  have hlower : N ^ 2 ≤ support.card * E := by
    have hcauchy := sq_sum_le_card_mul_sum_sq (s := support) (f := c)
    rw [hsumc, hsumsq] at hcauchy
    exact hcauchy
  have hupper : q * O ≤ N * (N - 1) := by
    simpa only [q, N, O] using hoff
  have hNpos : 0 < N := by simpa only [N] using Nat.pos_of_ne_zero hA
  have hcombined : q * N ^ 2 ≤
      support.card * (q * N + N * (N - 1)) := by
    calc
      q * N ^ 2 ≤ q * (support.card * E) := Nat.mul_le_mul_left q hlower
      _ = support.card * (q * N + q * O) := by rw [hE]; ring
      _ ≤ support.card * (q * N + N * (N - 1)) := by
        exact Nat.mul_le_mul_left support.card (Nat.add_le_add_left hupper (q * N))
  have hleft : q * N ^ 2 = N * (N * q) := by ring
  have hright : support.card * (q * N + N * (N - 1)) =
      N * (support.card * (q + N - 1)) := by
    have hN : 1 ≤ N := hNpos
    rw [show q + N - 1 = q + (N - 1) by omega]
    ring
  rw [hleft, hright] at hcombined
  refine ⟨v, ?_⟩
  rw [← hYeq]
  simpa only [q, N] using Nat.le_of_mul_le_mul_left hcombined hNpos
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
