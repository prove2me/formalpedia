-- Prove2me | solution 1 for QuarterSumLadder.gi_ne_neg_gi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:24.206512+00:00
-- url     : https://prove2.me/submissions/c567daed-3b5d-444a-988a-230e4d272bbf

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
theorem _root_.solution : gi ≠ -gi := by
  intro h; have := congrArg Zsqrtd.im h; simp at this
end QuarterSumLadder
