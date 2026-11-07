-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.anchored_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:30.974126+00:00
-- url     : https://prove2.me/submissions/c82d67df-4292-48cd-afe8-d08f3ad18f75

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_card_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} = 0) (R : Finset V) (m : Nat) :
    (anchored G R m).card ≤ R.card := by
  simpa using anchored_card_le G 0 (fun r => (hd r).le) R m
end QEC.Locality.ConnectedSetCounting
