-- Prove2me | solution 1 for QuarterSumLadder.R_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:12.986529+00:00
-- url     : https://prove2.me/submissions/8fb59c89-b4f7-42f5-9d2c-ad52fed56fc5

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_R_eq
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
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : R χ 0 = ((fiber χ 1).filter fun x => 4 * x.val < p).card := by
  simpa using R_eq (χ := χ) 0
end QuarterSumLadder
