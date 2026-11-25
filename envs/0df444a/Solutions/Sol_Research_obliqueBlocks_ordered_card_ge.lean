-- Prove2me | solution 1 for Research.obliqueBlocks_ordered_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:23:46.913133+00:00
-- url     : https://prove2.me/submissions/b9872092-7e60-49f3-908f-d59f062c5a36

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_radiusSixDirected_card_eq_twice_ordered
public import Theorems.Thm_Research_obliqueBlocks_directed_card_ge

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m : ℕ) :
    m * 8393309 ≤ (radiusSixOrderedPairs (obliqueBlocks m)).card := by
  have hlower := obliqueBlocks_directed_card_ge m
  have hdouble := radiusSixDirected_card_eq_twice_ordered (obliqueBlocks m)
  rw [hdouble] at hlower
  have htwice :
      2 * (m * 8393309) ≤
        2 * (radiusSixOrderedPairs (obliqueBlocks m)).card := by
    convert hlower using 1; ring
  exact Nat.le_of_mul_le_mul_left htwice (by norm_num)
end Research
