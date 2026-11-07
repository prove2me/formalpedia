-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.anchored_eq_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:16:48.730077+00:00
-- url     : https://prove2.me/submissions/c1c78418-fe8f-4fec-91bb-da1eb02d6431

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_rooted
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_anchored

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (R : Finset V) (m : Nat) :
    anchored G R m = R.biUnion (fun r => rooted G r m) := by
  classical
  ext A
  simp only [mem_anchored,Finset.mem_biUnion,mem_rooted]
  constructor
  · rintro ⟨hm,hc,r,hr⟩
    exact ⟨r,(Finset.mem_inter.mp hr).2,(Finset.mem_inter.mp hr).1,hm,hc⟩
  · rintro ⟨r,hrR,hrA,hm,hc⟩
    exact ⟨hm,hc,r,Finset.mem_inter.mpr ⟨hrA,hrR⟩⟩
end QEC.Locality.ConnectedSetCounting
