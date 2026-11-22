-- Prove2me | solution 1 for SZ.rec2_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:42:12.986312+00:00
-- url     : https://prove2.me/submissions/de564a91-2944-4658-805a-1bc762c90699

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (A B t₀ t₁ : ℤ) (n : ℕ) :
    rec2 A B t₀ t₁ (n + 2) = A * rec2 A B t₀ t₁ (n + 1) + B * rec2 A B t₀ t₁ n := rfl
end SZ
