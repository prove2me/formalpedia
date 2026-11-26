-- Prove2me | solution 1 for TunnellMap.odd_sq_eq_one_add_eight_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:00.264058+00:00
-- url     : https://prove2.me/submissions/3dc6c94b-55be-47e5-9a91-646980a0ee47

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {x : ℤ} (hx : Odd x) :
    ∃ k : ℤ, x ^ 2 = 1 + 8 * k := by
  rcases hx with ⟨a, ha⟩
  rcases Int.even_mul_succ_self a with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    x ^ 2 = (2 * a + 1) ^ 2 := by rw [ha]
    _ = 1 + 4 * (a * (a + 1)) := by ring
    _ = 1 + 8 * k := by rw [hk]; ring
end TunnellMap
