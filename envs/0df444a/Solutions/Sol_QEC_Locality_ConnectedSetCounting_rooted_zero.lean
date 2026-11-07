-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.rooted_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:21:58.625972+00:00
-- url     : https://prove2.me/submissions/d6aca4d0-0046-41da-94ef-6239e678969a

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_mem_rooted

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (r : V) : rooted G r 0 = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro A hA
  obtain ⟨hr,hm,hc⟩ := (mem_rooted G r 0 A).mp hA
  have he : A = ∅ := Finset.card_eq_zero.mp hm
  simpa [he] using hr
end QEC.Locality.ConnectedSetCounting
