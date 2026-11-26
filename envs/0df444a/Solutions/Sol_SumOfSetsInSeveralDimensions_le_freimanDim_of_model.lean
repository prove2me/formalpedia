-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.le_freimanDim_of_model
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:59.958964+00:00
-- url     : https://prove2.me/submissions/26ac95fe-dd61-4f4b-87bd-7eb6bd1620c1

module
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [DecidableEq G] [AddCommMonoid G] {X : Finset G} {d : ℕ}
    (hd : d ≤ #X) (hmodel : freimanModelDim X d) : d ≤ freimanDim X := by
  classical
  exact Nat.le_findGreatest hd hmodel
end SumOfSetsInSeveralDimensions
