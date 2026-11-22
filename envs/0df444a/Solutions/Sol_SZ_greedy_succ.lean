-- Prove2me | solution 1 for SZ.greedy_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:46:24.491589+00:00
-- url     : https://prove2.me/submissions/50cbd900-f65b-4f96-bcec-96ac0bcd3629

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (α : ℝ) (n : ℕ) :
    greedy α (n + 1) = 2 * ⌈α * (greedy α n : ℝ) / 2⌉ := rfl
end SZ
