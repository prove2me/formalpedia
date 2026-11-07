-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.anchored_one_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:24.340291+00:00
-- url     : https://prove2.me/submissions/0b5be72b-99bd-469d-b974-2cf4084a60c1

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_eq_biUnion
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_rooted_one

section
noncomputable section
namespace QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
private theorem anchored_one_family (G : SimpleGraph V) (R : Finset V) :
    anchored G R 1 = R.image (fun v => ({v} : Finset V)) := by
  rw [anchored_eq_biUnion]
  ext K
  simp only [Finset.mem_biUnion,rooted_one,Finset.mem_singleton,Finset.mem_image]
  constructor
  · rintro ⟨r,hr,hK⟩
    exact ⟨r,hr,hK.symm⟩
  · rintro ⟨r,hr,hK⟩
    exact ⟨r,hr,hK.symm⟩
end QEC.Locality.WeightedConnectedSetMass
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (G : SimpleGraph V) (R : Finset V) (a : V → ℝ) :
    anchoredMass G R 1 a = ∑ r ∈ R, a r := by
  unfold anchoredMass
  rw [anchored_one_family,Finset.sum_image]
  · simp
  · intro r _ s _ h
    exact Finset.singleton_injective h
end QEC.Locality.WeightedConnectedSetMass
