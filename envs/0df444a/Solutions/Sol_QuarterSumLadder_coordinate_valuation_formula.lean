-- Prove2me | solution 1 for QuarterSumLadder.coordinate_valuation_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:19:50.884649+00:00
-- url     : https://prove2.me/submissions/89135ff0-9323-4ad8-aeb1-d00668f7f99f

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_coordinate_valuation


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValInt 2 (x ^ 2 + y ^ 2) =
      2 * min (padicValInt 2 x) (padicValInt 2 y) +
        if padicValInt 2 x = padicValInt 2 y then 1 else 0 :=
  coordinate_valuation hx hy
end QuarterSumLadder
