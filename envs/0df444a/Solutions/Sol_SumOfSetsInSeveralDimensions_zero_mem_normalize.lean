-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.zero_mem_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:53.163577+00:00
-- url     : https://prove2.me/submissions/a7326870-0f2c-4889-a1a6-f0f92eda18f8

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize
section
public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
private lemma lexMin_mem {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : lexMin S hS ∈ S := by
  obtain ⟨x, hx, hxmin⟩ := mem_image.1 (min'_mem (S.image toLex) (hS.image toLex))
  rwa [lexMin, ← hxmin, ofLex_toLex]
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : 0 ∈ normalize S hS :=
  mem_image.2 ⟨lexMin S hS, lexMin_mem hS, sub_self _⟩
end SumOfSetsInSeveralDimensions
