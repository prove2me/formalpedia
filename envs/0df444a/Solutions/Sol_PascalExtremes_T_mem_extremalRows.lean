-- Prove2me | solution 1 for PascalExtremes.T_mem_extremalRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:54.247051+00:00
-- url     : https://prove2.me/submissions/70688188-1a32-4d1c-a111-6d170cd7c7b5

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Theorems.Thm_PascalExtremes_extremalRows_nonempty

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    T p m ∈ extremalRows p m := by
  exact Nat.sInf_mem (extremalRows_nonempty hp hm2 hpm)
end PascalExtremes
