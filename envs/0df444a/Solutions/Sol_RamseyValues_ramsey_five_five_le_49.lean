-- Prove2me | solution 1 for RamseyValues.ramsey_five_five_le_49
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T21:55:25.294535+00:00
-- url     : https://prove2.me/submissions/a241afad-0cbe-41ab-bb96-dc77ab8703ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey
import Theorems.Thm_RamseyValues_ramsey_four_five
import Theorems.Thm_LefebvreVariations_ramsey_five_five_regular_forty_nine

set_option autoImplicit false


open Erdos77

/-- The Ramsey property, for every finite vertex type with at least `n` vertices. -/
private def RP (a b n : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α], n ≤ Fintype.card α → ∀ G : SimpleGraph α,
    (∃ s : Finset α, G.IsNClique a s) ∨ (∃ s : Finset α, Gᶜ.IsNClique b s)

private lemma RP_mono {a b n n' : ℕ} (h : RP a b n) (hn : n ≤ n') : RP a b n' :=
  fun α _ hc G => h α (hn.trans hc) G

private lemma RP_iff_mem (a b n : ℕ) :
    RP a b n ↔ n ∈ {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ s : Finset (Fin n), G.IsNClique a s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique b s)} := by
  constructor
  · intro h G
    exact h (Fin n) (by simp) G
  · intro h α _ hc G
    let f : Fin n ↪ α := (Fin.castLEEmb hc).trans (Fintype.equivFin α).symm.toEmbedding
    have hcomp : (G.comap f)ᶜ = Gᶜ.comap f := by
      ext u v; simp [f.injective.ne_iff]
    rcases h (G.comap f) with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨s.map f, (hs.map).mono (SimpleGraph.map_comap_le _ _)⟩
    · rw [hcomp] at hs
      exact Or.inr ⟨s.map f, (hs.map).mono (SimpleGraph.map_comap_le _ _)⟩

/-- Swapping the roles of cliques and independent sets (pass to the complement). -/
private lemma RP_symm {a b n : ℕ} (h : RP a b n) : RP b a n := by
  intro α _ hc G
  rcases h α hc Gᶜ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inr ⟨s, hs⟩
  · rw [compl_compl] at hs
    exact Or.inl ⟨s, hs⟩

/-- Lift a clique of the neighbourhood of `v` in `H` to a clique of `H` containing `v`. -/
private lemma lift_insert {α : Type} [DecidableEq α] (H : SimpleGraph α) (v : α) (c : ℕ)
    (s : Finset (H.neighborSet v))
    (h : (H.comap (Function.Embedding.subtype _)).IsNClique c s) :
    H.IsNClique (c + 1) (insert v (s.map (Function.Embedding.subtype _))) := by
  refine ((h.map).mono (SimpleGraph.map_comap_le _ _)).insert ?_
  intro b hb
  simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
  obtain ⟨w, -, rfl⟩ := hb
  exact w.2

/-- Lift a clique of the complement of an induced subgraph. -/
private lemma lift_compl {α : Type} (H : SimpleGraph α) (S : Set α) (c : ℕ)
    (s : Finset S)
    (h : (H.comap (Function.Embedding.subtype (· ∈ S)))ᶜ.IsNClique c s) :
    Hᶜ.IsNClique c (s.map (Function.Embedding.subtype _)) := by
  have hcomp : (H.comap (Function.Embedding.subtype (· ∈ S)))ᶜ
      = Hᶜ.comap (Function.Embedding.subtype (· ∈ S)) := by
    ext u v; simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj,
      Function.Embedding.coe_subtype, ne_eq, Subtype.ext_iff]
  rw [hcomp] at h
  exact (h.map).mono (SimpleGraph.map_comap_le _ _)

/-- In a graph with no `a`-clique and no independent `b`-set, every degree is
below `n1` whenever `RP (a-1) b n1`. -/
private lemma deg_lt {a b n1 : ℕ} (ha : 1 ≤ a) (h1 : RP (a - 1) b n1)
    {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hA : ¬ ∃ s : Finset α, G.IsNClique a s) (hB : ¬ ∃ s : Finset α, Gᶜ.IsNClique b s)
    (v : α) : G.degree v < n1 := by
  by_contra hN
  push Not at hN
  have hN' : n1 ≤ Fintype.card (G.neighborSet v) := by
    rwa [SimpleGraph.card_neighborSet_eq_degree]
  rcases h1 (G.neighborSet v) hN' (G.comap (Function.Embedding.subtype _)) with
    ⟨s, hs⟩ | ⟨s, hs⟩
  · have := lift_insert G v (a - 1) s hs
    rw [Nat.sub_add_cancel ha] at this
    exact hA ⟨_, this⟩
  · exact hB ⟨_, lift_compl G (G.neighborSet v) b s hs⟩


/-- `R(4,5) ≤ 25` as a Ramsey property, read off the platform milestone `ramsey_four_five`. -/
private lemma RP45 : RP 4 5 25 := by
  have h := RamseyValues.ramsey_four_five
  have hne : (Erdos77.asymmetricRamsey 4 5) ≠ 0 := by omega
  have hmem := Nat.sInf_mem (Nat.nonempty_of_pos_sInf (Nat.pos_of_ne_zero hne))
  rw [RP_iff_mem]
  have : Erdos77.asymmetricRamsey 4 5 ∈ {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ s : Finset (Fin n), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin n), Gᶜ.IsNClique 5 s)} := hmem
  rwa [h] at this

/-- Degree window of a `(5,5)`-graph on `n` vertices, given `R(4,5) ≤ 25`: the neighbourhood of
`v` is a `(4,5)`-graph (so `deg v ≤ 24`) and so is the non-neighbourhood in the complement
(so `n - 1 - deg v ≤ 24`). -/
private lemma window {n : ℕ} (h45 : RP 4 5 25) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : ¬ ∃ s : Finset (Fin n), G.IsNClique 5 s)
    (hB : ¬ ∃ s : Finset (Fin n), Gᶜ.IsNClique 5 s) (v : Fin n) :
    n - 25 ≤ G.degree v ∧ G.degree v ≤ 24 := by
  classical
  have h1 := deg_lt (a := 5) (b := 5) (by norm_num) h45 G hA hB v
  have h2 := deg_lt (a := 5) (b := 5) (by norm_num) h45 Gᶜ hB (by rwa [compl_compl]) v
  have h3 := SimpleGraph.degree_compl G v
  simp only [Fintype.card_fin] at h3
  omega

/-- Conditional reduction: `R(4,5) ≤ 25` plus the variation give `R(5,5) ≤ 49`. -/
private lemma RP55 (h45 : RP 4 5 25) : RP 5 5 49 := by
  classical
  rw [RP_iff_mem]
  intro G
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hw := window h45 G hA hB
  rcases LefebvreVariations.ramsey_five_five_regular_forty_nine G (fun v => by have := hw v; omega) with h | h
  · exact hA h
  · exact hB h

-- Axioms of the conditional reduction: the gap axiom only through the variation.

theorem solution : Erdos77.asymmetricRamsey 5 5 ≤ 49 :=
  Nat.sInf_le ((RP_iff_mem _ _ _).mp (RP55 RP45))
