-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.mem_rooted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:22.178649+00:00
-- url     : https://prove2.me/submissions/351753a3-4d16-4459-9123-c007975f3276

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
theorem _root_.solution (G : SimpleGraph V) (r : V) (m : Nat) (A : Finset V) :
    A ∈ rooted G r m ↔ r ∈ A ∧ A.card = m ∧ (G.induce (A : Set V)).Connected := by
  classical
  simp [rooted]
end QEC.Locality.ConnectedSetCounting
