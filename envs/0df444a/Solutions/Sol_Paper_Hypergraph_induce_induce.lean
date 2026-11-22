-- Prove2me | solution 1 for Paper.Hypergraph.induce_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:51:35.96004+00:00
-- url     : https://prove2.me/submissions/b2531403-f153-4d5a-af50-3a8eac35241c

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (W U : Finset ℕ) :
    (H.induce W).induce U = H.induce (W ∩ U) := by
  have hv : (H.vertices ∩ W) ∩ U = H.vertices ∩ (W ∩ U) := inter_assoc _ _ _
  have he : (H.edges.filter (fun e => (H.edge e ∩ W).Nonempty)).filter
      (fun e => ((H.edge e ∩ W) ∩ U).Nonempty) =
      H.edges.filter (fun e => (H.edge e ∩ (W ∩ U)).Nonempty) := by
    ext e
    simp only [mem_filter, inter_assoc]
    constructor
    · tauto
    · rintro ⟨he, v, hv⟩
      exact ⟨⟨he, v, mem_inter.mpr ⟨(mem_inter.mp hv).1, (mem_inter.mp (mem_inter.mp hv).2).1⟩⟩, v, hv⟩
  cases H
  simp only [induce] at hv he ⊢
  congr 1
  funext e
  exact inter_assoc _ _ _
end Paper.Hypergraph
