-- Prove2me | solution 1 for PerfectGraph.card_inter_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:47.456732+00:00
-- url     : https://prove2.me/submissions/1aaa4a9b-819e-46a6-823c-e1f3686384ab

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution [DecidableEq V] {K A : Finset V} (hK : G.IsClique (K : Set V))
    (hA : G.IsIndepSet (A : Set V)) : (K ∩ A).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  rw [Finset.mem_inter] at ha hb
  exact hA ha.2 hb.2 hab (hK ha.1 hb.1 hab)
end PerfectGraph
