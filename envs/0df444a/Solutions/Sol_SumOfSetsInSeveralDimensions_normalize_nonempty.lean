-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.normalize_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:48.220372+00:00
-- url     : https://prove2.me/submissions/7e2bdf3d-123f-49d7-8eee-ed9202a27a01

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
public import Theorems.Thm_SumOfSetsInSeveralDimensions_zero_mem_normalize

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) :
    (normalize S hS).Nonempty :=
  ⟨0, zero_mem_normalize hS⟩
end SumOfSetsInSeveralDimensions
