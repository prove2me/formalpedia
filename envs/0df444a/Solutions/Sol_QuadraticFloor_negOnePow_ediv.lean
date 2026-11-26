-- Prove2me | solution 1 for QuadraticFloor.negOnePow_ediv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:46:19.995801+00:00
-- url     : https://prove2.me/submissions/4856a374-8e29-4229-94fe-b2d680bfc326

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
public import Theorems.Thm_QuadraticFloor_odd_of_ne_two

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) (v C : ℤ) (hv : Even (v - C)) :
    ((v / (p : ℤ)).negOnePow : ℤ) = (C.negOnePow : ℤ) * ((v % (p : ℤ)).negOnePow : ℤ) := by
  obtain ⟨k, hk⟩ := odd_of_ne_two hp2
  have h1 : (v / (p : ℤ)).negOnePow = ((p : ℤ) * (v / (p : ℤ))).negOnePow := by
    rw [Int.negOnePow_eq_iff]
    refine ⟨-(k * (v / (p : ℤ))), ?_⟩
    rw [show (p : ℤ) = 2 * k + 1 by exact_mod_cast hk]
    ring
  have h2 : (p : ℤ) * (v / (p : ℤ)) = v - v % (p : ℤ) := by
    have := Int.emod_add_mul_ediv v (p : ℤ); linarith
  have h3 : v.negOnePow = C.negOnePow := (Int.negOnePow_eq_iff _ _).2 hv
  rw [h1, h2, Int.negOnePow_sub, h3, Units.val_mul]
end QuadraticFloor
