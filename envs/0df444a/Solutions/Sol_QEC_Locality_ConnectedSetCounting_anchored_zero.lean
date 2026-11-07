-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.anchored_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:23:34.006213+00:00
-- url     : https://prove2.me/submissions/8c788be7-0afe-4b0c-bfaa-98ed1807b6ea

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_eq_biUnion
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_rooted_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (R : Finset V) : anchored G R 0 = ∅ := by
  classical
  rw [anchored_eq_biUnion]
  apply Finset.eq_empty_of_forall_notMem
  intro A hA
  obtain ⟨r,hr,hroot⟩ := Finset.mem_biUnion.mp hA
  rw [rooted_zero] at hroot
  simpa using hroot
end QEC.Locality.ConnectedSetCounting
