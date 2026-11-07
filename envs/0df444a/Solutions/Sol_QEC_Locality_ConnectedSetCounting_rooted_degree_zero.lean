-- Prove2me | solution 1 for QEC.Locality.ConnectedSetCounting.rooted_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:25.136865+00:00
-- url     : https://prove2.me/submissions/c5cc0554-b498-48ff-82ff-139c9be3654c

import Definitions.Def_QEC_Locality_Graph_Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Theorems.Thm_QEC_Locality_ConnectedSetCounting_rooted_card_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.ConnectedSetCounting
open Classical
open scoped BigOperators
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.ConnectedSetCounting
theorem _root_.solution (G : SimpleGraph V)
    (hd : ∀ r, Nat.card {w : V // G.Adj r w} = 0) (r : V) (m : Nat) :
    (rooted G r m).card ≤ 1 := by
  simpa using rooted_card_le G 0 (fun v => (hd v).le) r m
end QEC.Locality.ConnectedSetCounting
