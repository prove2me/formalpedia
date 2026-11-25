-- Prove2me | solution 1 for SmallRatio.recipTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:58.214471+00:00
-- url     : https://prove2.me/submissions/5c459af6-dce9-4ff4-a4db-46b167754e3a

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
public import Theorems.Thm_SmallRatio_den_pos
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_den_identity


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ steps k h) :
    recipTerm k h i = (k : ℚ) / ((rem k h i : ℚ) * den k h i) +
      (-(den k h (i - 1) : ℚ) / den k h i + (rem k h i : ℚ) / rem k h (i - 1)
        + 1 / ((rem k h i : ℚ) * rem k h (i - 1)) - 3) := by
  have e := rem_den_identity hh hhk hc (show i - 1 ≤ steps k h by omega)
  rw [show i - 1 + 1 = i by omega] at e
  have hr : (rem k h i : ℚ) ≠ 0 := by exact_mod_cast (pos_rem_of_le_steps hh hhk hc hi).ne'
  have hd : (den k h i : ℚ) ≠ 0 := by
    have := den_pos hh hhk hc hi1 (by omega); exact_mod_cast (by omega : den k h i ≠ 0)
  have hr' : (rem k h (i - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (pos_rem_of_le_steps hh hhk hc (show i - 1 ≤ steps k h by omega)).ne'
  have eQ : (k : ℚ) = (rem k h (i - 1) : ℚ) * den k h i + (rem k h i : ℚ) * den k h (i - 1) := by
    exact_mod_cast e.symm
  unfold recipTerm
  rw [eQ]
  field_simp
  ring
end SmallRatio
