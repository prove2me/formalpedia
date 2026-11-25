-- Prove2me | solution 1 for PerfectGraph.cliqueNum_induce_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:31:51.44536+00:00
-- url     : https://prove2.me/submissions/348c74ae-b164-4bdd-b791-35b5bb5babaf

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_card_le_cliqueNum_induce
public import Theorems.Thm_PerfectGraph_exists_clique_card_eq_cliqueNum_induce

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution [Finite V] {S T : Finset V} (h : T ⊆ S) :
    (G.induce (T : Set V)).cliqueNum ≤ (G.induce (S : Set V)).cliqueNum := by
  obtain ⟨K, hKT, hK, hc⟩ := exists_clique_card_eq_cliqueNum_induce G T
  rw [← hc]
  exact card_le_cliqueNum_induce G (hKT.trans h) hK
end PerfectGraph
