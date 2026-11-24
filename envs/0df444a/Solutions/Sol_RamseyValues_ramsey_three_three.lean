-- Prove2me | solution 1 for RamseyValues.ramsey_three_three
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:43:11.561744+00:00
-- url     : https://prove2.me/submissions/018b985e-45b8-4994-8cad-374861b09a56

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

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

/-- `R(2, b) ≤ b`: an edge, or the whole vertex set is independent. -/
private lemma RP_two (b : ℕ) : RP 2 b b := by
  classical
  intro α _ hc G
  by_cases h : ∃ u v, G.Adj u v
  · obtain ⟨u, v, huv⟩ := h
    left
    refine ⟨{u, v}, ⟨?_, ?_⟩⟩
    · rw [Finset.coe_pair]; exact SimpleGraph.isClique_pair.mpr (fun _ => huv)
    · exact Finset.card_pair huv.ne
  · push Not at h
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α))
      (by simpa using hc)
    right
    refine ⟨s, ⟨?_, hs⟩⟩
    intro x _ y _ hxy
    exact (SimpleGraph.compl_adj G x y).mpr ⟨hxy, h x y⟩

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

/-- The pigeonhole step (Erdős–Szekeres). -/
private lemma RP_step {a b n1 n2 : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : RP (a - 1) b n1) (h2 : RP a (b - 1) n2) (hpos : 0 < n1 + n2) :
    RP a b (n1 + n2) := by
  classical
  intro α _ hc G
  have hcard : 0 < Fintype.card α := lt_of_lt_of_le hpos hc
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hcard
  have hdeg := SimpleGraph.degree_compl G v
  by_cases hN : n1 ≤ G.degree v
  · have hN' : n1 ≤ Fintype.card (G.neighborSet v) := by
      rwa [SimpleGraph.card_neighborSet_eq_degree]
    rcases h1 (G.neighborSet v) hN' (G.comap (Function.Embedding.subtype _)) with
      ⟨s, hs⟩ | ⟨s, hs⟩
    · left
      have := lift_insert G v (a - 1) s hs
      rw [Nat.sub_add_cancel ha] at this
      exact ⟨_, this⟩
    · right
      exact ⟨_, lift_compl G (G.neighborSet v) b s hs⟩
  · have hM : n2 ≤ Gᶜ.degree v := by omega
    have hM' : n2 ≤ Fintype.card (Gᶜ.neighborSet v) := by
      rwa [SimpleGraph.card_neighborSet_eq_degree]
    rcases h2 (Gᶜ.neighborSet v) hM' (Gᶜ.comap (Function.Embedding.subtype _))ᶜ with
      ⟨s, hs⟩ | ⟨s, hs⟩
    · left
      have := lift_compl Gᶜ (Gᶜ.neighborSet v) a s hs
      rw [compl_compl] at this
      exact ⟨_, this⟩
    · right
      rw [compl_compl] at hs
      have := lift_insert Gᶜ v (b - 1) s hs
      rw [Nat.sub_add_cancel hb] at this
      exact ⟨_, this⟩

private lemma RP33 : RP 3 3 6 := RP_step (n1 := 3) (n2 := 3) (by norm_num) (by norm_num)
  (RP_two 3) (RP_symm (RP_two 3)) (by norm_num)

/-- A lower bound: if `RP a b N` fails while some `RP a b M` holds, then `N < R(a,b)`. -/
private lemma lt_ramsey {a b N M : ℕ} (hN : ¬ RP a b N) (hM : RP a b M) :
    N < Erdos77.asymmetricRamsey a b := by
  have hR : RP a b (Erdos77.asymmetricRamsey a b) := by
    rw [RP_iff_mem]
    exact Nat.sInf_mem ⟨M, (RP_iff_mem a b M).mp hM⟩
  by_contra hle
  push Not at hle
  exact hN (RP_mono hR hle)

private lemma three_of_clique {α : Type} [DecidableEq α] {H : SimpleGraph α} {s : Finset α}
    (h : H.IsNClique 3 s) : ∃ a b c, H.Adj a b ∧ H.Adj a c ∧ H.Adj b c := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h.card_eq
  exact ⟨a, b, c, h.1 (by simp) (by simp) hab, h.1 (by simp) (by simp) hac,
    h.1 (by simp) (by simp) hbc⟩

/-! The pentagon `C₅` on `ZMod 5`: `i ~ j` iff `i - j = ±1`. -/

private def pm5 (d : ℕ) : Bool := d == 1 || d == 4

private lemma pm5_symm : ∀ i j : Fin 5, pm5 ((i.val + 5 - j.val) % 5) = true →
    pm5 ((j.val + 5 - i.val) % 5) = true := by decide

private lemma pm5_irrefl : ∀ i : Fin 5, ¬ pm5 ((i.val + 5 - i.val) % 5) = true := by
  decide

private def C5 : SimpleGraph (Fin 5) where
  Adj i j := pm5 ((i.val + 5 - j.val) % 5) = true
  symm := ⟨pm5_symm⟩
  loopless := ⟨pm5_irrefl⟩

private instance : DecidableRel C5.Adj := fun _ _ => inferInstanceAs (Decidable (_ = true))

private lemma C5_noK3 : ∀ a b c : Fin 5, C5.Adj a b → C5.Adj a c → C5.Adj b c → False := by
  decide

private lemma C5c_noK3 : ∀ a b c : Fin 5, C5ᶜ.Adj a b → C5ᶜ.Adj a c → C5ᶜ.Adj b c → False := by
  decide

private lemma not_RP33_5 : ¬ RP 3 3 5 := by
  intro h
  rcases h (Fin 5) (by simp) C5 with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨a, b, c, h1, h2, h3⟩ := three_of_clique hs
    exact C5_noK3 a b c h1 h2 h3
  · obtain ⟨a, b, c, h1, h2, h3⟩ := three_of_clique hs
    exact C5c_noK3 a b c h1 h2 h3

theorem solution : Erdos77.asymmetricRamsey 3 3 = 6 := by
  have hup : Erdos77.asymmetricRamsey 3 3 ≤ 6 := Nat.sInf_le ((RP_iff_mem _ _ _).mp RP33)
  have hlo := lt_ramsey not_RP33_5 RP33
  omega
