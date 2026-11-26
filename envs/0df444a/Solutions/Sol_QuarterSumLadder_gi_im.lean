-- Prove2me | solution 1 for QuarterSumLadder.gi_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:53:52.706256+00:00
-- url     : https://prove2.me/submissions/7b1a4457-cb98-4cd6-9eca-712042ca2bb7

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
theorem _root_.solution : gi.im = 1 := rfl
end QuarterSumLadder
