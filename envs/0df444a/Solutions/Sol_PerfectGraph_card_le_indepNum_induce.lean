-- Prove2me | solution 1 for PerfectGraph.card_le_indepNum_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:35:54.39819+00:00
-- url     : https://prove2.me/submissions/3822f809-bf2f-470c-b49d-bf2ed9abcad6

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_card_le_cliqueNum_induce
public import Theorems.Thm_PerfectGraph_indepNum_induce_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution [Finite V] {S K : Finset V} (hKS : K ⊆ S)
    (hK : G.IsIndepSet (K : Set V)) :
    K.card ≤ (G.induce (S : Set V)).indepNum := by
  rw [indepNum_induce_eq]
  exact card_le_cliqueNum_induce Gᶜ hKS (by simpa using hK)
end PerfectGraph
