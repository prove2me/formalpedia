-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.anchored_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:13.62282+00:00
-- url     : https://prove2.me/submissions/c934772e-8859-4bae-b628-33a77ce2d8b0

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_rooted_card_le
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_anchored_eq_biUnion

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V) (Delta : Nat)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} ≤ Delta) (R : Finset V) (m : Nat) :
    (anchored G R m).card ≤ R.card * (Delta+1)^(2*m) := by
  classical
  rw [anchored_eq_biUnion]
  calc
    (R.biUnion (fun r => rooted G r m)).card ≤ ∑ r ∈ R, (rooted G r m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, (Delta+1)^(2*m) := by
      apply Finset.sum_le_sum
      intro r hr
      exact rooted_card_le G Delta hd r m
    _ = R.card * (Delta+1)^(2*m) := by simp
end QEC.Locality.ConnectedSetCounting
