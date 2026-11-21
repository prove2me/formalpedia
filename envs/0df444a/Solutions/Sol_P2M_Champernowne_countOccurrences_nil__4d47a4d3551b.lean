-- Prove2me | solution 1 for P2M_Champernowne_countOccurrences_nil__4d47a4d3551b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:35:36.076269+00:00
-- url     : https://prove2.me/submissions/d00b9e86-7dcc-4769-9890-4e44918f24ad

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (w : List ℕ) :
    countOccurrences w [] = if w.isPrefixOf [] then 1 else 0 := by
  simp [countOccurrences]
end Champernowne
