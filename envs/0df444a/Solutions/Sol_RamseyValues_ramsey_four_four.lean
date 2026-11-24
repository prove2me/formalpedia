-- Prove2me | solution 1 for RamseyValues.ramsey_four_four
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:43:14.2118+00:00
-- url     : https://prove2.me/submissions/6007e844-ca7e-4e8a-893d-c9dad4f603b9

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

/-- Greenwood–Gleason parity step: if `R(a-1,b)` and `R(a,b-1)` bounds `n1`, `n2` are
both even, then `R(a,b) ≤ n1 + n2 - 1`. On exactly `n1 + n2 - 1` vertices a bad graph
would be `(n1 - 1)`-regular of odd order and odd degree, contradicting the handshake
lemma. -/
private lemma RP_parity {a b n1 n2 : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h1 : RP (a - 1) b n1) (h2 : RP a (b - 1) n2) (hpos : 0 < n1)
    (he1 : Even n1) (he2 : Even n2) : RP a b (n1 + n2 - 1) := by
  classical
  intro α _ hc G
  rcases Nat.lt_or_ge (n1 + n2 - 1) (Fintype.card α) with hlt | hle
  · exact RP_step ha hb h1 h2 (by omega) α (by omega) G
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hcard : Fintype.card α = n1 + n2 - 1 := by omega
  have hd1 : ∀ v, G.degree v < n1 := deg_lt ha h1 G hA hB
  have hd2 : ∀ v, Gᶜ.degree v < n2 :=
    deg_lt hb (RP_symm h2) Gᶜ hB (by rwa [compl_compl])
  have hdeg : ∀ v, G.degree v = n1 - 1 := by
    intro v
    have h3 := SimpleGraph.degree_compl G v
    have h4 := hd1 v
    have h5 := hd2 v
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard] at hsum
  have hev : Even ((n1 + n2 - 1) * (n1 - 1)) := ⟨G.edgeFinset.card, by omega⟩
  obtain ⟨p, hp⟩ := he1
  obtain ⟨q, hq⟩ := he2
  rcases Nat.even_mul.mp hev with ⟨r, hr⟩ | ⟨r, hr⟩ <;> omega

private lemma RP33 : RP 3 3 6 := RP_step (n1 := 3) (n2 := 3) (by norm_num) (by norm_num)
  (RP_two 3) (RP_symm (RP_two 3)) (by norm_num)

private lemma RP34 : RP 3 4 9 := RP_parity (n1 := 4) (n2 := 6) (by norm_num) (by norm_num)
  (RP_two 4) RP33 (by norm_num) (by decide) (by decide)

private lemma RP44 : RP 4 4 18 := RP_step (n1 := 9) (n2 := 9) (by norm_num) (by norm_num)
  RP34 (RP_symm RP34) (by norm_num)

/-- A lower bound: if `RP a b N` fails while some `RP a b M` holds, then `N < R(a,b)`. -/
private lemma lt_ramsey {a b N M : ℕ} (hN : ¬ RP a b N) (hM : RP a b M) :
    N < Erdos77.asymmetricRamsey a b := by
  have hR : RP a b (Erdos77.asymmetricRamsey a b) := by
    rw [RP_iff_mem]
    exact Nat.sInf_mem ⟨M, (RP_iff_mem a b M).mp hM⟩
  by_contra hle
  push Not at hle
  exact hN (RP_mono hR hle)

private lemma four_of_clique {α : Type} [DecidableEq α] {H : SimpleGraph α} {s : Finset α}
    (h : H.IsNClique 4 s) : ∃ a b c d, H.Adj a b ∧ H.Adj a c ∧ H.Adj b c ∧
      H.Adj a d ∧ H.Adj b d ∧ H.Adj c d := by
  have hc := h.card_eq
  obtain ⟨d, hd⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have h3 : (s.erase d).card = 3 := by rw [Finset.card_erase_of_mem hd]; omega
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp h3
  have ha : a ∈ s.erase d := by rw [he]; simp
  have hb : b ∈ s.erase d := by rw [he]; simp
  have hc' : c ∈ s.erase d := by rw [he]; simp
  rw [Finset.mem_erase] at ha hb hc'
  exact ⟨a, b, c, d, h.1 ha.2 hb.2 hab, h.1 ha.2 hc'.2 hac, h.1 hb.2 hc'.2 hbc,
    h.1 ha.2 hd ha.1, h.1 hb.2 hd hb.1, h.1 hc'.2 hd hc'.1⟩

/-! The Paley graph on `ZMod 17`: `i ~ j` iff `i - j` is a nonzero square mod 17. -/

private def qr17 (d : ℕ) : Bool :=
  d == 1 || d == 2 || d == 4 || d == 8 || d == 9 || d == 13 || d == 15 || d == 16

private lemma qr17_symm : ∀ i j : Fin 17, qr17 ((i.val + 17 - j.val) % 17) = true →
    qr17 ((j.val + 17 - i.val) % 17) = true := by decide

private lemma qr17_irrefl : ∀ i : Fin 17, ¬ qr17 ((i.val + 17 - i.val) % 17) = true := by
  decide

private def P17 : SimpleGraph (Fin 17) where
  Adj i j := qr17 ((i.val + 17 - j.val) % 17) = true
  symm := ⟨qr17_symm⟩
  loopless := ⟨qr17_irrefl⟩

private instance : DecidableRel P17.Adj := fun _ _ => inferInstanceAs (Decidable (_ = true))

private lemma P17_noK4 : ∀ a b c d : Fin 17, P17.Adj a b → P17.Adj a c → P17.Adj b c →
    P17.Adj a d → P17.Adj b d → P17.Adj c d → False := by decide

private lemma P17c_noK4 : ∀ a b c d : Fin 17, P17ᶜ.Adj a b → P17ᶜ.Adj a c → P17ᶜ.Adj b c →
    P17ᶜ.Adj a d → P17ᶜ.Adj b d → P17ᶜ.Adj c d → False := by decide

private lemma not_RP44_17 : ¬ RP 4 4 17 := by
  intro h
  rcases h (Fin 17) (by simp) P17 with ⟨s, hs⟩ | ⟨s, hs⟩
  · obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩ := four_of_clique hs
    exact P17_noK4 a b c d h1 h2 h3 h4 h5 h6
  · obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6⟩ := four_of_clique hs
    exact P17c_noK4 a b c d h1 h2 h3 h4 h5 h6

theorem solution : Erdos77.asymmetricRamsey 4 4 = 18 := by
  have hup : Erdos77.asymmetricRamsey 4 4 ≤ 18 := Nat.sInf_le ((RP_iff_mem _ _ _).mp RP44)
  have hlo := lt_ramsey not_RP44_17 RP44
  omega
