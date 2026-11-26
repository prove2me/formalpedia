-- Prove2me | solution 1 for QuarterSumLadder.distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:55.12546+00:00
-- url     : https://prove2.me/submissions/372d1285-8a81-4549-bb4a-56310f57a680

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
theorem _root_.solution :
    ((1 : GaussianInt) = gi ↔ False) ∧ ((1 : GaussianInt) = -1 ↔ False) ∧
    ((1 : GaussianInt) = -gi ↔ False) ∧ (gi = 1 ↔ False) ∧ (gi = -1 ↔ False) ∧
    (gi = -gi ↔ False) ∧ ((-1 : GaussianInt) = 1 ↔ False) ∧ ((-1 : GaussianInt) = gi ↔ False) ∧
    ((-1 : GaussianInt) = -gi ↔ False) ∧ (-gi = 1 ↔ False) ∧ (-gi = gi ↔ False) ∧
    (-gi = (-1 : GaussianInt) ↔ False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [iff_false] <;> decide
end QuarterSumLadder
