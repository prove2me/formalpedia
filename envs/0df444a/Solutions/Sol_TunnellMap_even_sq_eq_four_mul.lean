-- Prove2me | solution 1 for TunnellMap.even_sq_eq_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:03.32575+00:00
-- url     : https://prove2.me/submissions/510236c4-c07d-4e7b-a9a3-0dc62f827965

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {x : ℤ} (hx : Even x) :
    ∃ k : ℤ, x ^ 2 = 4 * k := by
  rcases hx with ⟨a, ha⟩
  refine ⟨a ^ 2, ?_⟩
  rw [ha]
  ring
end TunnellMap
