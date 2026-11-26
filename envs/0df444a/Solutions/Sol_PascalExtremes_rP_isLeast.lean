-- Prove2me | solution 1 for PascalExtremes.rP_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:00.950302+00:00
-- url     : https://prove2.me/submissions/1672b535-3300-40b1-94d7-3013e4ded035

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers
public import Theorems.Thm_PascalExtremes_one_le_rP
public import Theorems.Thm_PascalExtremes_lt_pow_rP
public import Theorems.Thm_PascalExtremes_rP_le_of_lt_pow

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution {p m : ℕ} (hp : 1 < p) (hm : m ≠ 0) :
    IsLeast {r : ℕ | 1 ≤ r ∧ m < p ^ r} (rP p m) := by
  refine ⟨⟨one_le_rP p m, lt_pow_rP hp⟩, ?_⟩
  intro s hs
  exact rP_le_of_lt_pow hp hm hs.2
end PascalExtremes
