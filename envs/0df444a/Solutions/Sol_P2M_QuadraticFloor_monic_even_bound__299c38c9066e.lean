-- Prove2me | solution 1 for P2M_QuadraticFloor_monic_even_bound__299c38c9066e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:05:42.253384+00:00
-- url     : https://prove2.me/submissions/785c5c27-df67-463c-94b8-b0c957c9f08c

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
public import Theorems.Thm_QuadraticFloor_osum_abs_le
public import Theorems.Thm_P2M_QuadraticFloor_monic_even__b68b70dddb0d

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (t b : ℤ) :
    |floorSum 1 (2 * t) b p| ≤ 1 + 2 * |t| := by
  rw [monic_even' hp2]
  have h1 : |(((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ)| = 1 := by
    rcases Int.isUnit_iff.1 (((b - t ^ 2) / (p : ℤ)).negOnePow.isUnit) with h | h <;> simp [h]
  have h2 := osum_abs_le t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ)) (by
    intro j
    rcases Int.isUnit_iff.1 (((j ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow.isUnit) with h | h <;>
      simp [h])
  calc _ ≤ |(((b - t ^ 2) / (p : ℤ)).negOnePow : ℤ)| +
        |2 * osum t (fun m => (((m ^ 2 + (b - t ^ 2)) / (p : ℤ)).negOnePow : ℤ))| := abs_sub _ _
    _ ≤ 1 + 2 * |t| := by rw [h1, abs_mul]; simp; linarith
end QuadraticFloor
