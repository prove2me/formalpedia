-- Prove2me | solution 1 for QuarterSumLadder.mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:59:41.925787+00:00
-- url     : https://prove2.me/submissions/5cad38a3-25ca-4b52-a981-9585cdbd4279

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} {x : ZMod p} {z : GaussianInt} :
    x ∈ fiber χ z ↔ χ x = z := by simp [fiber]
end QuarterSumLadder
