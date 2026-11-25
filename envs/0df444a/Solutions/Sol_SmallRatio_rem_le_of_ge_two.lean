-- Prove2me | solution 1 for SmallRatio.rem_le_of_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:42.946389+00:00
-- url     : https://prove2.me/submissions/6d92fb85-f26b-4361-9e31-0a72a1359e2b

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_rem_add_two_lt
attribute [local simp] SmallRatio.rem_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.den_one

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
namespace SmallRatio
theorem _root_.solution (j : ℕ) (hge : ∀ i ≤ j + 1, 2 ≤ rem k h i) : rem k h (j + 1) + j ≤ h := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih (fun i hi => hge i (by omega))
    have h2 : rem k h (j + 1 + 1) < rem k h (j + 1) :=
      rem_add_two_lt (k := k) (h := h) j (by have := hge (j + 1) (by omega); omega)
    omega
end SmallRatio
