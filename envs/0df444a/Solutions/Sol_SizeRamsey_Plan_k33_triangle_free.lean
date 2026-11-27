-- Prove2me | solution 1 for SizeRamsey.Plan.k33_triangle_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:17.589613+00:00
-- url     : https://prove2.me/submissions/9010df27-6ba6-448e-a976-0aefa2671905

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution :
    ∀ a b c, k33MinusEdge.Adj a b →
      k33MinusEdge.Adj b c → ¬ k33MinusEdge.Adj c a := by
  decide
end SizeRamsey.Plan
