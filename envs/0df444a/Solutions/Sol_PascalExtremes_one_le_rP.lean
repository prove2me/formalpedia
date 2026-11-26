-- Prove2me | solution 1 for PascalExtremes.one_le_rP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:55:43.816414+00:00
-- url     : https://prove2.me/submissions/9ec8ef71-34d2-43bf-8731-211ed39d0c31

module
public import Mathlib
public import Definitions.Def_PascalExtremes_Powers

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution (p m : ℕ) : 1 ≤ rP p m := by
  simp [rP]
end PascalExtremes
