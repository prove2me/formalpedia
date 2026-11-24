-- Prove2me | solution 1 for RamseyValues.ramsey_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:12:29.295828+00:00
-- url     : https://prove2.me/submissions/135b34b6-515c-4233-ba83-d8b693416cd3

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

/-- The pigeonhole step. -/
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

/-- Ramsey's theorem: every `RP a b ·` holds for some `n`. -/
private lemma RP_exists : ∀ s a b : ℕ, a + b = s → ∃ n, RP a b n := by
  intro s
  induction s with
  | zero =>
    intro a b hs
    refine ⟨0, fun α _ _ G => Or.inl ⟨∅, ?_⟩⟩
    simp; omega
  | succ s ih =>
    intro a b hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨0, fun α _ _ G => Or.inl ⟨∅, by simp⟩⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact ⟨0, fun α _ _ G => Or.inr ⟨∅, by simp⟩⟩
    obtain ⟨n1, h1⟩ := ih (a - 1) b (by omega)
    obtain ⟨n2, h2⟩ := ih a (b - 1) (by omega)
    exact ⟨n1 + 1 + n2, RP_step ha hb (RP_mono h1 (by omega)) h2 (by omega)⟩

private lemma RP_ramsey (a b : ℕ) : RP a b (Erdos77.asymmetricRamsey a b) := by
  obtain ⟨n, hn⟩ := RP_exists (a + b) a b rfl
  rw [RP_iff_mem]
  exact Nat.sInf_mem ⟨n, (RP_iff_mem a b n).mp hn⟩

private lemma ramsey_pos {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < Erdos77.asymmetricRamsey a b := by
  rcases Nat.eq_zero_or_pos (Erdos77.asymmetricRamsey a b) with h | h
  · have := RP_ramsey a b
    rw [h] at this
    rcases this (Fin 0) (by simp) ⊥ with ⟨s, hs⟩ | ⟨s, hs⟩
    · have := hs.card_eq
      have : s.card ≤ 0 := by simpa using Finset.card_le_univ s
      omega
    · have := hs.card_eq
      have : s.card ≤ 0 := by simpa using Finset.card_le_univ s
      omega
  · exact h

theorem solution (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    Erdos77.asymmetricRamsey k l ≤
      Erdos77.asymmetricRamsey (k - 1) l + Erdos77.asymmetricRamsey k (l - 1) := by
  have hpos := ramsey_pos (a := k - 1) (b := l) (by omega) (by omega)
  have h := RP_step (by omega) (by omega) (RP_ramsey (k - 1) l) (RP_ramsey k (l - 1))
    (by omega)
  exact Nat.sInf_le ((RP_iff_mem _ _ _).mp h)
