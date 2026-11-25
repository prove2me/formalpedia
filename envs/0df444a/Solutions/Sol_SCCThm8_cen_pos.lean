-- Prove2me | solution 1 for SCCThm8.cen_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:24.162242+00:00
-- url     : https://prove2.me/submissions/5cd0e982-54a0-40de-9582-1f548c14e567

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) : 0 < cen k := Nat.choose_pos (by omega)
end SCCThm8
