-- Prove2me | solution 1 for P2M_QuadraticFloor_monic_odd__8e05b6979b8c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:49.974638+00:00
-- url     : https://prove2.me/submissions/55f864e5-48bb-482d-b12c-90c9eac2e03c

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_eq_of_osum_step
public import Theorems.Thm_QuadraticFloor_osum_add
public import Theorems.Thm_QuadraticFloor_osum_mul_left
public import Theorems.Thm_QuadraticFloor_osum_negOnePow
public import Theorems.Thm_QuadraticFloor_sum_range_shift
public import Theorems.Thm_QuadraticFloor_Fodd_succ
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (t b : ℤ) :
    floorSum 1 (2 * t + 1) b p = (floorSum 1 1 0 p - 1) + ((b - t * (t + 1)).negOnePow : ℤ) -
      2 * osum (b - t * (t + 1)) (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) := by
  set b' := b - t * (t + 1)
  -- shift `n ↦ n + t`
  have hshift : floorSum 1 (2 * t + 1) b p = Fodd p b' := by
    unfold Fodd floorSum
    set g : ℤ → ℤ := fun m => (((1 * m ^ 2 + 1 * m + b') / (p : ℤ)).negOnePow : ℤ)
    have hg : ∀ m, g (m + p) = g m := by
      intro m
      simp only [g]
      rw [show 1 * (m + p) ^ 2 + 1 * (m + p) + b' = (1 * m ^ 2 + 1 * m + b') + (p : ℤ) * (2 * m + p + 1)
        by ring, Int.add_mul_ediv_left _ _ (by exact_mod_cast hp.out.ne_zero), Int.negOnePow_add,
        Int.negOnePow_even (2 * m + p + 1) (by
          obtain ⟨k, hk⟩ := odd_of_ne_two hp2
          exact ⟨m + k + 1, by rw [hk]; push_cast; ring⟩), mul_one]
    have := sum_range_shift hg t
    simp only [g] at this
    rw [← this]
    apply sum_congr rfl
    intro n _
    congr 3
    simp only [b']; ring
  have hF := eq_of_osum_step (F := Fodd p)
    (g := fun c => -2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3)))
    (Fodd_succ hp2) b'
  rw [hshift, hF]
  have hsplit : osum b' (fun c => -2 * (c.negOnePow : ℤ) * (1 + legendreSym p (-4 * c - 3))) =
      -2 * osum b' (fun j => (j.negOnePow : ℤ)) +
        -2 * osum b' (fun j => (j.negOnePow : ℤ) * legendreSym p (-4 * j - 3)) := by
    rw [← osum_mul_left, ← osum_mul_left, ← osum_add]
    congr 1; funext j; ring
  rw [hsplit]
  have h1 := osum_negOnePow b'
  unfold Fodd
  linarith
end QuadraticFloor
