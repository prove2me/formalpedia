-- Prove2me | solution 1 for PerfectGraph.exists_indepSet_card_eq_indepNum_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:35:56.465465+00:00
-- url     : https://prove2.me/submissions/bf55c232-ed03-4f94-a502-e669eab571f0

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_exists_clique_card_eq_cliqueNum_induce
public import Theorems.Thm_PerfectGraph_indepNum_induce_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution (S : Finset V) :
    ∃ K ⊆ S, G.IsIndepSet (K : Set V) ∧ K.card = (G.induce (S : Set V)).indepNum := by
  obtain ⟨K, hKS, hK, hc⟩ := exists_clique_card_eq_cliqueNum_induce Gᶜ S
  exact ⟨K, hKS, by simpa using hK, by rw [hc, indepNum_induce_eq]⟩
end PerfectGraph
