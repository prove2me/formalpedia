-- Prove2me | solution 1 for QuarterSumLadder.gauss_lehmer_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:18:01.327805+00:00
-- url     : https://prove2.me/submissions/889348ab-eefc-4140-b4cf-9864d87b8e25

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_gauss_product


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) (A : Finset (ZMod p))
    (hA : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p)
    (hφ : ∀ x ∈ A, (if 4 * x.val < p then 2 * x else -(2 * x)) ∈ A) :
    (2 : ZMod p) ^ A.card * (-1) ^ (A.filter fun x => ¬ 4 * x.val < p).card = 1 :=
  gauss_product hp2 A hA hφ
end QuarterSumLadder
