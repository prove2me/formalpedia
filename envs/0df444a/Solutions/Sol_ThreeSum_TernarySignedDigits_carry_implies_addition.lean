-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.carry_implies_addition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:44.238394+00:00
-- url     : https://prove2.me/submissions/7b51d5bc-f800-41a9-bc5a-fd11214080ec

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_evaluate_digits_of_lt
import Theorems.Thm_ThreeSum_TernarySignedDigits_evaluate_carry
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution {b J x y z : ℕ} (hx : x<b^J) (hy : y<b^J) (hz : z<b^J)
    {c : CarryWord J} (hc : ValidCarry c) (hd : DigitRelation b J x y z c) : x+y=z := by
  have hs : evaluate b J (fun j => (digit b x j : ℤ)+(digit b y j : ℤ))=
      evaluate b J (fun j => (digit b z j : ℤ)+((b : ℤ)*carryAt c (j+1)-carryAt c j)) := by
    apply sum_congr rfl
    intro j hj
    have hh := hd ⟨j,mem_range.mp hj⟩
    congr 1
    dsimp at hh
    linarith
  have hadd (f g : ℕ → ℤ) : evaluate b J (fun j => f j+g j)=evaluate b J f+evaluate b J g := by
    simp only [evaluate,add_mul,sum_add_distrib]
  rw [hadd,hadd,evaluate_digits_of_lt hx,evaluate_digits_of_lt hy,evaluate_digits_of_lt hz,
    evaluate_carry,hc.1,hc.2] at hs
  norm_num at hs
  exact_mod_cast hs
end ThreeSum.TernarySignedDigits
