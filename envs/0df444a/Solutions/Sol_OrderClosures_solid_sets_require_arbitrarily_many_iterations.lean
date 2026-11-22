-- Prove2me | solution 1 for OrderClosures.solid_sets_require_arbitrarily_many_iterations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:04.738746+00:00
-- url     : https://prove2.me/submissions/d112f3ff-c676-4376-b5f3-184aacd09c6a

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
public import Theorems.Thm_OrderClosures_gaoIterationTower_strict
public import Theorems.Thm_OrderClosures_solidGeneratorNumber_gaoIterationSet

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v
namespace OrderClosures
theorem _root_.solution
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (ξ : Ordinal.{u})
    (hξ : ξ ≤ Cardinal.ord (Order.succ κ)) :
    ∃ (X : Type (u + 1)) (_ : AddCommGroup X) (_ : Lattice X)
      (_ : IsOrderedAddMonoid X) (_ : VectorLattice X),
      ∃ S : Set X, LatticeOrderedAddCommGroup.IsSolid S ∧
        solidGeneratorNumber S = Cardinal.lift.{u + 1, u} κ ∧
          NeedsOrderAdherenceIterations S (Ordinal.lift.{u + 1, u} ξ) := by
  let S := gaoIterationSet κ hκ
  refine ⟨GaoIterationProduct κ, inferInstance, inferInstance, inferInstance,
    inferInstance, S, LatticeOrderedAddCommGroup.isSolid_solidClosure _,
    solidGeneratorNumber_gaoIterationSet κ hκ, ?_⟩
  refine ⟨canonicalOrderAdherenceTower S, ?_⟩
  intro η hη
  exact gaoIterationTower_strict κ hκ η
    (hη.trans_le (Ordinal.lift_le.mpr hξ))
end OrderClosures
