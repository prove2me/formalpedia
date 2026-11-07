-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.occupied_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:12.838296+00:00
-- url     : https://prove2.me/submissions/9e709a14-eea3-42d4-87d9-77fcf46a16c3

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
theorem _root_.solution (G : SimpleGraph V) (R B : Finset V) (hRB : Disjoint R B)
    (a : V → ℝ) : occupiedMass G R B 1 a=∑ r ∈ R, a r := by
  unfold occupiedMass
  rw [anchored_one_family,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r hr
    have hn : r∉B := fun h => Finset.disjoint_left.mp hRB hr h
    have hs : ({r} : Finset V) \ B = {r} := by
      ext v
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · exact fun h => h.1
      · intro hv
        exact ⟨hv,by simpa only [hv] using hn⟩
    rw [hs,Finset.prod_singleton]
  · intro r _ t _ h
    exact Finset.singleton_injective h
end QEC.Locality.WeightedConnectedSetMass
