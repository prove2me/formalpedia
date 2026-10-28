-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T07:56:20.927049+00:00
-- url     : https://prove2.me/submissions/bc2677a8-cc75-458c-be50-111ac4e8ebe2

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_2

open PathsTreesFlowers.Invariance

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (J : AltTree G) :
    J.outer.card = J.inner.card + 1 ∧
    (∀ v ∈ J.outer, ∃! N : Finset E,
      IsMaxMatchingIn G J.toSub N ∧ ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G N w ↔ w = v)) ∧
    (∀ N : Finset E, IsMaxMatchingIn G J.toSub N →
      ∃ v ∈ J.outer, ∀ w ∈ J.verts, (PathsTreesFlowers.Duality.IsExposed G N w ↔ w = v)) := by
  let JD : PathsTreesFlowers.Duality.AltTree G :=
    { inner := J.inner
      outer := J.outer
      edges := J.edges
      disjoint := J.disjoint_inner_outer
      edge_ends := J.edge_inner_outer
      inner_deg := J.inner_degree
      connected := ⟨J.verts_eq ▸ J.connected.1, fun u hu w hw => J.connected.2 u (J.verts_eq ▸ hu) w (J.verts_eq ▸ hw)⟩
      card_verts := J.verts_eq ▸ J.card_verts }
  have h := PathsTreesFlowers.Duality.lemma_4_2 G JD
  have hverts : J.verts = JD.verts := J.verts_eq
  rw [hverts]
  exact h
