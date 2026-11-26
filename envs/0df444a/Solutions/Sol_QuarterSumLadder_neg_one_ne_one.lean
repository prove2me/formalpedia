-- Prove2me | solution 1 for QuarterSumLadder.neg_one_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:38.221615+00:00
-- url     : https://prove2.me/submissions/b82146bd-f30d-4b02-82db-b4a1ca4c991d

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_im
attribute [local simp] QuarterSumLadder.gi_re
attribute [local simp] QuarterSumLadder.gi_im

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution : (-1 : GaussianInt) ≠ 1 := by
  intro h; have := congrArg Zsqrtd.re h; simp at this
end QuarterSumLadder
