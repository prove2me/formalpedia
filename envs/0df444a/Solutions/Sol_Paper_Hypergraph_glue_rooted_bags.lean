-- Prove2me | solution 1 for Paper.Hypergraph.glue_rooted_bags
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:20.49493+00:00
-- url     : https://prove2.me/submissions/d67d9864-44a0-4ee1-9b0c-6661df9c0d3f

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_finite_rooted_tree_decomposition
import Theorems.Thm_Paper_Hypergraph_rooted_forest_tree

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {I : Type*} [Fintype I]
    {V : I → Type*} [∀ i, Fintype (V i)]
    (G : ∀ i, SimpleGraph (V i)) (hG : ∀ i, (G i).IsTree)
    (bag : ∀ i, V i → Finset ℕ) (root : ∀ i, V i) (o : I)
    (hsub : ∀ i t, bag i t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ i t, H.edge e ⊆ bag i t)
    (hvertex : ∀ v ∈ H.vertices, ∃ i t, v ∈ bag i t)
    (hrun : ∀ i v, (G i |>.induce {t | v ∈ bag i t}).Preconnected)
    (hlocal : ∀ i t, bag i t ∩ bag o (root o) ⊆ bag i (root i))
    (hoverlap : ∀ i j, i ≠ j → ∀ a c, bag i a ∩ bag j c ⊆ bag o (root o))
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ i t, b (bag i t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∃ t, bag o (root o) ⊆ D.bag t ∧
      ∀ t, b (D.bag t) ≤ r := by
  classical
  obtain ⟨F, hF, hGF, hstar⟩ := rooted_forest_tree G hG root o
  letI : Nonempty (Sigma V) := ⟨⟨o, root o⟩⟩
  let bags : Sigma V → Finset ℕ := fun t => bag t.1 t.2
  have hwithin (i : I) (v : ℕ) (a c : V i) (ha : v ∈ bag i a) (hc : v ∈ bag i c) :
      (F.induce {t | v ∈ bags t}).Reachable ⟨⟨i, a⟩, ha⟩ ⟨⟨i, c⟩, hc⟩ := by
    let f : (G i).induce {t | v ∈ bag i t} →g F.induce {t | v ∈ bags t} := {
      toFun := fun t => ⟨⟨i, t.val⟩, t.property⟩
      map_rel' := fun hab => hGF ⟨rfl, hab⟩ }
    exact (hrun i v ⟨a, ha⟩ ⟨c, hc⟩).map f
  apply H.finite_rooted_tree_decomposition F hF bags (fun t => hsub t.1 t.2)
    (by intro e he; obtain ⟨i,t,ht⟩ := hedge e he; exact ⟨⟨i,t⟩, ht⟩)
    (by intro v hv; obtain ⟨i,t,ht⟩ := hvertex v hv; exact ⟨⟨i,t⟩, ht⟩)
    _ ⟨o,root o⟩ (bag o (root o)) (Subset.refl _) b r (fun t => hwidth t.1 t.2)
  intro v hv a c
  by_cases hi : a.val.1 = c.val.1
  · obtain ⟨⟨i,a⟩,ha⟩ := a
    obtain ⟨⟨j,c⟩,hc⟩ := c
    dsimp at hi
    subst j
    exact hwithin i v a c ha hc
  · have hvroot : v ∈ bag o (root o) := hoverlap _ _ hi _ _ (mem_inter.mpr ⟨a.property,c.property⟩)
    have htoc (t : {t : Sigma V // v ∈ bags t}) :
        (F.induce {t | v ∈ bags t}).Reachable t ⟨⟨o,root o⟩,hvroot⟩ := by
      obtain ⟨⟨i,t⟩,ht⟩ := t
      have hri : v ∈ bag i (root i) := hlocal i t (mem_inter.mpr ⟨ht,hvroot⟩)
      have hh := hwithin i v t (root i) ht hri
      by_cases hio : i = o
      · subst i
        exact hh
      · exact hh.trans (show (F.induce {t | v ∈ bags t}).Adj
          ⟨⟨i,root i⟩,hri⟩ ⟨⟨o,root o⟩,hvroot⟩ from (hstar i hio).symm).reachable
    exact (htoc a).trans (htoc c).symm
end Paper.Hypergraph
