-- Prove2me | solution 1 for RamanujanNested.rollUp_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T04:59:27.764037+00:00
-- url     : https://prove2.me/submissions/439b632d-7394-4898-9e75-0dd644ad8ede

module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_RamanujanNested_Defs

set_option autoImplicit true
@[expose] public section
open RamanujanNested
namespace RamanujanNested
theorem _root_.solution (a : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    rollUp a T (n + 1) = Real.sqrt (1 + a 1 * rollUp (fun k => a (k + 1)) T n) := rfl
end RamanujanNested
