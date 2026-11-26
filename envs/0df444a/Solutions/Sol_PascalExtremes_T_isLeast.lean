-- Prove2me | solution 1 for PascalExtremes.T_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:36.29146+00:00
-- url     : https://prove2.me/submissions/a45766b5-da56-4893-bb73-815f1374de2c

module
public import Definitions.Def_PascalExtremes_TargetA
public import Mathlib
public import Definitions.Def_PascalExtremes_TargetAAttainment
public import Theorems.Thm_PascalExtremes_T_mem_extremalRows

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p m : ℕ} (hp : p.Prime) (hm2 : 2 ≤ m) (hpm : ¬ p ∣ m) :
    IsLeast (extremalRows p m) (T p m) := by
  refine ⟨T_mem_extremalRows hp hm2 hpm, ?_⟩
  intro N hN
  exact Nat.sInf_le hN
end PascalExtremes
