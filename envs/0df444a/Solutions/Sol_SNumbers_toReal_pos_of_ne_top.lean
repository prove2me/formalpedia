-- Prove2me | solution 1 for SNumbers.toReal_pos_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:08:36.097491+00:00
-- url     : https://prove2.me/submissions/0b76688d-0ee6-4bee-aabb-86884cf40207

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one Fact.out).ne' hp
end SNumbers
