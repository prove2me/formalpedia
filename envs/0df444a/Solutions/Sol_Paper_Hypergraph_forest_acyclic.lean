-- Prove2me | solution 1 for Paper.Hypergraph.forest_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:56:56.41626+00:00
-- url     : https://prove2.me/submissions/97e465d3-b752-4100-9894-c599dc38930d

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
theorem _root_.solution {I : Type*} {V : I → Type*} (G : ∀ i, SimpleGraph (V i))
    (hG : ∀ i, (G i).IsAcyclic) : (forestGraph G).IsAcyclic := by
  have hsupp : ∀ {a b : Sigma V} (p : (forestGraph G).Walk a b),
      ∀ z ∈ p.support, z.1 = a.1 := by
    intro a b p
    induction p with
    | nil => simp
    | @cons a b c hab p ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · rfl
      · exact (ih z hz).trans hab.choose.symm
  intro a p hp
  let q := p.induce {z : Sigma V | z.1 = a.1} (hsupp p)
  have hq : q.IsCycle := by
    apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (f := (SimpleGraph.Embedding.induce {z : Sigma V | z.1 = a.1}).toHom)
      (by intro a b h; exact Subtype.ext h)).mp
    have heq : q.map (SimpleGraph.Embedding.induce {z : Sigma V | z.1 = a.1}).toHom = p :=
      SimpleGraph.Walk.map_induce p _
    rw [heq]
    exact hp
  exact hG a.1 _ (hq.map (f := (forestFiberIso G a.1).toHom)
    (forestFiberIso G a.1).injective)
end Paper.Hypergraph
