-- Prove2me | solution 1 for Paper.Hypergraph.finite_rooted_tree_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:26.649854+00:00
-- url     : https://prove2.me/submissions/9f1ab647-f9ef-4639-95c2-70d268717889

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
theorem _root_.solution (H : Hypergraph) {T : Type*} [Fintype T] [Nonempty T]
    (G : SimpleGraph T) (hG : G.IsTree) (bag : T → Finset ℕ)
    (hsub : ∀ t, bag t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ t, H.edge e ⊆ bag t)
    (hvertex : ∀ v ∈ H.vertices, ∃ t, v ∈ bag t)
    (hrun : ∀ v ∈ H.vertices, (G.induce {t | v ∈ bag t}).Preconnected)
    (root : T) (Z : Finset ℕ) (hroot : Z ⊆ bag root)
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ t, b (bag t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∃ root, Z ⊆ D.bag root ∧
      ∀ t, b (D.bag t) ≤ r := by
  classical
  let n := Fintype.card T - 1
  have hcard : Fintype.card T = n + 1 := by
    dsimp [n]
    have := Fintype.card_pos (α := T)
    omega
  let e : Fin (n + 1) ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨n, {
    tree := G.comap e
    isTree := (SimpleGraph.Iso.comap e G).isTree_iff.mpr hG
    bag := fun t => bag (e t)
    bag_subset := fun t => hsub (e t)
    edge_covered := ?_
    vertex_covered := ?_
    running_intersection := ?_ }, e.symm root, by simpa using hroot, fun t => hwidth (e t)⟩
  · intro f hf
    obtain ⟨t, ht⟩ := hedge f hf
    exact ⟨e.symm t, by simpa using ht⟩
  · intro v hv
    obtain ⟨t, ht⟩ := hvertex v hv
    exact ⟨e.symm t, by simpa using ht⟩
  · intro v hv a c
    let f : G.induce {t | v ∈ bag t} →g
        (G.comap e).induce {t | v ∈ bag (e t)} := {
      toFun := fun t => ⟨e.symm t, by
        change v ∈ bag (e (e.symm t.val))
        rw [e.apply_symm_apply]
        exact t.property⟩
      map_rel' := by
        intro a b hab
        change G.Adj (e (e.symm a.val)) (e (e.symm b.val))
        rw [e.apply_symm_apply, e.apply_symm_apply]
        exact hab }
    have hh := (hrun v hv ⟨e a, a.property⟩ ⟨e c, c.property⟩).map f
    have ha : f ⟨e a, a.property⟩ = a := Subtype.ext (e.symm_apply_apply a)
    have hc : f ⟨e c, c.property⟩ = c := Subtype.ext (e.symm_apply_apply c)
    rw [ha, hc] at hh
    exact hh
end Paper.Hypergraph
