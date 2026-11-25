-- Prove2me | solution 1 for Research.obliquePatch_ordered_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:20:06.783429+00:00
-- url     : https://prove2.me/submissions/e5ec4804-d13f-4c06-b22b-3a86302d47ce

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_obliquePatch_directed_card_ge
public import Theorems.Thm_Research_radiusSixDirected_card_eq_twice_ordered

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution :
    8393309 ≤ (radiusSixOrderedPairs obliquePoint).card := by
  have hlower := obliquePatch_directed_card_ge
  have hdouble := radiusSixDirected_card_eq_twice_ordered obliquePoint
  rw [hdouble] at hlower
  omega
end Research
