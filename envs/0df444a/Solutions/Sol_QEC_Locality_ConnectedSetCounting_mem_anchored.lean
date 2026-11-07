-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.mem_anchored
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:15:26.738208+00:00
-- url     : https://prove2.me/submissions/39ec12d4-8780-4183-b185-7aaf47ffd3c6

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (R : Finset V) (m : Nat) (A : Finset V) :
    A ∈ anchored G R m ↔ A.card = m ∧
      (G.induce (A : Set V)).Connected ∧ (A ∩ R).Nonempty := by
  classical
  simp [anchored]
end QEC.Locality.ConnectedSetCounting
