-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.normalize_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:36.26987+00:00
-- url     : https://prove2.me/submissions/9f4185bf-99da-4fc3-b0cc-98d97239f283

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
public import Mathlib.Tactic.Abel
public import Definitions.Def_SumOfSetsInSeveralDimensions_Normalize

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : #(normalize S hS) = #S :=
  card_image_of_injective _ (sub_left_injective (b := lexMin S hS))
end SumOfSetsInSeveralDimensions
