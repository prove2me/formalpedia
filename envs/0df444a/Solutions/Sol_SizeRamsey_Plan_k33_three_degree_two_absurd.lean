-- Prove2me | solution 1 for SizeRamsey.Plan.k33_three_degree_two_absurd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:57.142002+00:00
-- url     : https://prove2.me/submissions/668240f7-4af2-459f-b624-ffc7a9b1714b

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution : ∀ x y z : Fin 6, x ≠ y → x ≠ z → y ≠ z →
    (x = 0 ∨ x = 3) → (y = 0 ∨ y = 3) → (z = 0 ∨ z = 3) → False := by
  decide
end SizeRamsey.Plan
