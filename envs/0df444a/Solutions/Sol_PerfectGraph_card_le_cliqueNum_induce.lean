-- Prove2me | solution 1 for PerfectGraph.card_le_cliqueNum_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:27:47.736103+00:00
-- url     : https://prove2.me/submissions/8292b39a-1ab6-43fd-a2a8-1702cc060345

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
theorem _root_.solution [Finite V] {S K : Finset V} (hKS : K ⊆ S)
    (hK : G.IsClique (K : Set V)) :
    K.card ≤ (G.induce (S : Set V)).cliqueNum := by
  classical
  let K' : Finset (S : Set V) := K.subtype (· ∈ (S : Set V))
  have hc : K'.card = K.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => by simpa using hKS hx)]
  have : (G.induce (S : Set V)).IsClique (K' : Set _) := by
    intro x hx y hy hxy
    simp only [K', Finset.mem_coe, Finset.mem_subtype] at hx hy
    simpa using hK hx hy (Subtype.coe_injective.ne hxy)
  rw [← hc]
  exact this.card_le_cliqueNum
end PerfectGraph
