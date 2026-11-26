-- Prove2me | solution 1 for QuarterSumLadder.gi_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:53:49.860227+00:00
-- url     : https://prove2.me/submissions/8c857357-a425-4432-95a9-e8c159277a83

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_QuarterSumLadder_Basic

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution : gi.re = 0 := rfl
end QuarterSumLadder
