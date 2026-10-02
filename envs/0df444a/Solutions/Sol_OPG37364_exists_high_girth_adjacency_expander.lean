-- Prove2me | solution 1 for OPG37364.exists_high_girth_adjacency_expander
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T16:14:00.561536+00:00
-- url     : https://prove2.me/submissions/3e2193c8-98a0-4b60-a220-5e9e8ed58194

import Theorems.Thm_OPG37364_exists_lps13_prime_above
import Theorems.Thm_OPG37364_lps13Graph_regular14
import Theorems.Thm_OPG37364_lps13Graph_bipartite
import Theorems.Thm_OPG37364_lps13_remaining_core
import Definitions.Def_opg37364_lps13
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false
open scoped Classical

namespace OPG37364.Stage95

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transport the original OPG reachability predicate through a graph isomorphism. -/
theorem connected_iso (e : G ≃g H) (h : IsConnected G) : IsConnected H := by
  rcases h with ⟨⟨v₀⟩, h⟩
  refine ⟨⟨e v₀⟩, ?_⟩
  intro u v
  have hp := (h (e.symm u) (e.symm v)).lift e
    (fun _ _ hadj => e.map_adj_iff.mpr hadj)
  simpa [Function.onFun] using hp

/-- The original Boolean coloring transports contravariantly. -/
theorem bipartite_iso (e : G ≃g H) (h : IsBipartite G) : IsBipartite H := by
  obtain ⟨side, hside⟩ := h
  refine ⟨side ∘ e.symm, ?_⟩
  intro u v hadj
  exact hside (e.symm.map_adj_iff.mpr hadj)

/-- Neighbor-set cardinality is preserved by the induced equivalence. -/
theorem regular_iso (e : G ≃g H) {d : ℕ} (h : IsRegularOfDegree G d) :
    IsRegularOfDegree H d := by
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  exact (Set.encard_congr (e.mapNeighborSet v)).symm.trans (h v)

/-- Map the original cyclic-list encoding, including its closing edge. -/
theorem cycleList_iso (e : G ≃g H) {vs : List V} (h : IsCycleList G vs) :
    IsCycleList H (vs.map e) := by
  obtain ⟨x, y, middle, hv, hlen, hnodup, hchain, hclose⟩ := h
  refine ⟨e x, e y, middle.map e, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hv]
  · simpa using hlen
  · exact hnodup.map e.injective
  · exact List.isChain_map_of_isChain e (fun _ _ ha => e.map_adj_iff.mpr ha) hchain
  · exact e.map_adj_iff.mpr hclose

/-- Pull cycles back through the inverse isomorphism, preserving their lengths. -/
theorem girth_iso (e : G ≃g H) {g : ℕ} (h : HasGirthAtLeast G g) :
    HasGirthAtLeast H g := by
  intro vs hvs
  simpa using h (vs.map e.symm) (cycleList_iso e.symm hvs)

/-- Relabeling the real adjacency matrix is an algebra equivalence, hence preserves spectrum. -/
theorem adjacency_spectrum_iso [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) :
    spectrum ℝ (H.adjMatrix ℝ) = spectrum ℝ (G.adjMatrix ℝ) := by
  rw [← e.reindex_adjMatrix ℝ]
  exact AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv) (G.adjMatrix ℝ)

/-- Stage 6's mod-four conclusion supplies the exact Stage 7 root subtype. -/
theorem root_nonempty {q : ℕ} [Fact q.Prime] (hmod : q ≡ 1 [MOD 4]) :
    Nonempty (LPS13Root q) := by
  have hm : q % 4 = 1 := hmod
  have hs : IsSquare (-1 : ZMod q) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  obtain ⟨i, hi⟩ := hs
  exact ⟨⟨i, by simpa only [pow_two] using hi.symm⟩⟩

/-- A nonempty fourteen-regular graph has at least two vertices. -/
theorem card_two_le_of_regular14 [Fintype V] [Nonempty V]
    (h : IsRegularOfDegree G 14) : 2 ≤ Fintype.card V := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hc := Set.encard_le_encard (Set.subset_univ (G.neighborSet v))
  rw [h v, Set.encard_univ, ENat.card_eq_coe_fintype_card] at hc
  have hn : 14 ≤ Fintype.card V := by exact_mod_cast hc
  omega

end OPG37364.Stage95

open OPG37364 OPG37364.Stage95

theorem solution :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
        HasGirthAtLeast G g ∧
        (∀ μ : ℝ, μ ∈ spectrum ℝ (G.adjMatrix ℝ) → μ ≠ 14 → μ < 12) := by
  intro g hg
  obtain ⟨B, hB⟩ := lps13_remaining_core g hg
  obtain ⟨q, hprime, hlarge, _hmod52, hmod4, hnr⟩ := exists_lps13_prime_above B
  letI : Fact q.Prime := ⟨hprime⟩
  have hq : 13 < q := lt_of_le_of_lt (le_max_right B 13) hlarge
  have hBq : B < q := lt_of_le_of_lt (le_max_left B 13) hlarge
  obtain ⟨i⟩ := root_nonempty hmod4
  letI : Fintype (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) := Fintype.ofFinite _
  let G := lps13Graph hq i
  obtain ⟨hconn, hgirth, hspec⟩ := hB q hq i hBq hnr
  have hreg : IsRegularOfDegree G 14 := lps13Graph_regular14 hq i
  have hbip : IsBipartite G := lps13Graph_bipartite hq i hnr
  let n := Fintype.card (Matrix.ProjGenLinGroup (Fin 2) (ZMod q))
  let H : SimpleGraph (Fin n) := G.overFin rfl
  let e : G ≃g H := G.overFinIso rfl
  refine ⟨n, card_two_le_of_regular14 hreg, H, connected_iso e hconn,
    bipartite_iso e hbip, regular_iso e hreg, girth_iso e hgirth, ?_⟩
  intro μ hμ hne
  exact hspec μ ((adjacency_spectrum_iso e) ▸ hμ) hne

