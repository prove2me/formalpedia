-- Prove2me | solution 1 for TwinWidthI.MinorFree.lexDFS_exists
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:26:11.321971+00:00
-- url     : https://prove2.me/submissions/54914d39-c269-4daf-a107-1754efbc555f

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace Aux_LexDFS
open TwinWidthI.MinorFree

section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The graph on the vertices not among the first `p` entries of `L`. -/
def undiscL (G : SimpleGraph V) (L : List V) (p : ℕ) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ p ≤ L.idxOf x ∧ p ≤ L.idxOf y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

noncomputable def wordL (G : SimpleGraph V) (v₁ : V) (L : List V) (p : ℕ) (x : V) :
    List Bool :=
  List.ofFn fun j : Fin p =>
    @decide (∃ c, p ≤ L.idxOf c ∧ (undiscL G L p).Reachable x c ∧ G.Adj c (L.getD j v₁))
      (Classical.propDecidable _)

def ActL (G : SimpleGraph V) (L : List V) (p : ℕ) (a : V) : Prop :=
  L.idxOf a < p ∧ (∃ w, p ≤ L.idxOf w ∧ G.Adj a w) ∧
    ∀ a', L.idxOf a' < p → (∃ w, p ≤ L.idxOf w ∧ G.Adj a' w) → L.idxOf a' ≤ L.idxOf a

def GoodL (G : SimpleGraph V) (v₁ : V) (L : List V) (p : ℕ) (v : V) : Prop :=
  ∃ a, ActL G L p a ∧ G.Adj a v ∧
    ∀ u, p ≤ L.idxOf u → G.Adj a u → wordL G v₁ L p u ≤ wordL G v₁ L p v

def ValidL (G : SimpleGraph V) (v₁ : V) (L : List V) : Prop :=
  L.Nodup ∧ L.head? = some v₁ ∧ ∀ p (h : p < L.length), 0 < p → GoodL G v₁ L p L[p]

theorem idx_append (L : List V) (u x : V) :
    (x ∈ L → (L ++ [u]).idxOf x = L.idxOf x) ∧
      (x ∉ L → L.length ≤ (L ++ [u]).idxOf x) := by
  constructor
  · intro hx
    rw [List.idxOf_append, if_pos hx]
  · intro hx
    rw [List.idxOf_append, if_neg hx]
    omega

theorem tr_lt (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length) (x : V) :
    (L ++ [u]).idxOf x < p ↔ L.idxOf x < p := by
  by_cases hx : x ∈ L
  · rw [(idx_append L u x).1 hx]
  · have h1 := (idx_append L u x).2 hx
    have h2 : L.idxOf x = L.length := List.idxOf_eq_length hx
    constructor <;> intro h <;> omega

theorem tr_ge (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length) (x : V) :
    p ≤ (L ++ [u]).idxOf x ↔ p ≤ L.idxOf x := by
  rw [← not_lt, ← not_lt, tr_lt L u p hp x]

theorem tr_eq (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length) (x : V)
    (hx : L.idxOf x < p) : (L ++ [u]).idxOf x = L.idxOf x := by
  have hxL : x ∈ L := List.idxOf_lt_length_iff.1 (by omega)
  exact (idx_append L u x).1 hxL

theorem act_tr (G : SimpleGraph V) (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length) (a : V) :
    ActL G (L ++ [u]) p a ↔ ActL G L p a := by
  unfold ActL
  constructor
  · rintro ⟨h1, ⟨w, hw, haw⟩, h3⟩
    have h1' := (tr_lt L u p hp a).1 h1
    refine ⟨h1', ⟨w, (tr_ge L u p hp w).1 hw, haw⟩, ?_⟩
    intro a' ha' hex
    obtain ⟨w', hw', haw'⟩ := hex
    have h4 := h3 a' ((tr_lt L u p hp a').2 ha') ⟨w', (tr_ge L u p hp w').2 hw', haw'⟩
    rwa [tr_eq L u p hp a' ha', tr_eq L u p hp a h1'] at h4
  · rintro ⟨h1, ⟨w, hw, haw⟩, h3⟩
    refine ⟨(tr_lt L u p hp a).2 h1, ⟨w, (tr_ge L u p hp w).2 hw, haw⟩, ?_⟩
    intro a' ha' hex
    obtain ⟨w', hw', haw'⟩ := hex
    have ha'' := (tr_lt L u p hp a').1 ha'
    have h4 := h3 a' ha'' ⟨w', (tr_ge L u p hp w').1 hw', haw'⟩
    rw [tr_eq L u p hp a' ha'', tr_eq L u p hp a h1]
    exact h4

theorem undisc_tr (G : SimpleGraph V) (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length) :
    undiscL G (L ++ [u]) p = undiscL G L p := by
  ext x y
  show (G.Adj x y ∧ p ≤ (L ++ [u]).idxOf x ∧ p ≤ (L ++ [u]).idxOf y) ↔
    (G.Adj x y ∧ p ≤ L.idxOf x ∧ p ≤ L.idxOf y)
  rw [tr_ge L u p hp x, tr_ge L u p hp y]

theorem word_tr (G : SimpleGraph V) (v₁ : V) (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length)
    (x : V) : wordL G v₁ (L ++ [u]) p x = wordL G v₁ L p x := by
  unfold wordL
  rw [undisc_tr G L u p hp]
  congr 1
  funext j
  have hj : (j : ℕ) < L.length := lt_of_lt_of_le j.isLt hp
  rw [List.getD_append L [u] v₁ j hj]
  have hP : (∃ c, p ≤ (L ++ [u]).idxOf c ∧ (undiscL G L p).Reachable x c ∧
        G.Adj c (L.getD j v₁)) ↔
      (∃ c, p ≤ L.idxOf c ∧ (undiscL G L p).Reachable x c ∧ G.Adj c (L.getD j v₁)) :=
    exists_congr (fun c => and_congr (tr_ge L u p hp c) Iff.rfl)
  rw [propext hP]

theorem good_tr (G : SimpleGraph V) (v₁ : V) (L : List V) (u : V) (p : ℕ) (hp : p ≤ L.length)
    (v : V) : GoodL G v₁ (L ++ [u]) p v ↔ GoodL G v₁ L p v := by
  unfold GoodL
  simp only [act_tr G L u p hp, tr_ge L u p hp, word_tr G v₁ L u p hp]

theorem valid_append (G : SimpleGraph V) (v₁ : V) (L : List V) (hv : ValidL G v₁ L) (u : V)
    (hu : u ∉ L) (hg : GoodL G v₁ L L.length u) : ValidL G v₁ (L ++ [u]) := by
  obtain ⟨hnd, hhd, hgood⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, List.nodup_singleton u, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hab
    subst hb
    exact hu ha
  · simp [List.head?_append, hhd]
  · intro p hp hp0
    have hp' : p < L.length + 1 := by simpa using hp
    rcases Nat.lt_or_ge p L.length with h | h
    · rw [List.getElem_append_left h]
      exact (good_tr G v₁ L u p h.le _).2 (hgood p h hp0)
    · have hpl : p = L.length := by omega
      subst hpl
      rw [List.getElem_concat_length rfl]
      exact (good_tr G v₁ L u L.length le_rfl u).2 hg

theorem exists_next (G : SimpleGraph V) (v₁ : V) (L : List V) (hconn : G.Connected)
    (hv : ValidL G v₁ L) (hlt : L.length < Fintype.card V) :
    ∃ u, u ∉ L ∧ GoodL G v₁ L L.length u := by
  classical
  obtain ⟨hnd, hhd, -⟩ := hv
  have hv1 : v₁ ∈ L := List.mem_of_mem_head? hhd
  obtain ⟨w, hw⟩ : ∃ w, w ∉ L := by
    by_contra h
    push_neg at h
    have h1 : L.toFinset = Finset.univ :=
      Finset.eq_univ_of_forall (fun x => List.mem_toFinset.2 (h x))
    have h2 := List.toFinset_card_of_nodup hnd
    rw [h1, Finset.card_univ] at h2
    omega
  obtain ⟨wk⟩ := hconn.preconnected v₁ w
  obtain ⟨d, -, hd1, hd2⟩ := wk.exists_boundary_dart {x | x ∈ L} hv1 hw
  have hSne : (Finset.univ.filter (fun a => a ∈ L ∧ ∃ w, w ∉ L ∧ G.Adj a w)).Nonempty :=
    ⟨d.fst, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd1, d.snd, hd2, d.adj⟩⟩
  obtain ⟨a, haS, hamax⟩ := Finset.exists_max_image _ (fun x => L.idxOf x) hSne
  obtain ⟨-, haL, w', hw'L, haw'⟩ := Finset.mem_filter.1 haS
  have hTne : (Finset.univ.filter (fun u => u ∉ L ∧ G.Adj a u)).Nonempty :=
    ⟨w', Finset.mem_filter.2 ⟨Finset.mem_univ _, hw'L, haw'⟩⟩
  obtain ⟨u, huT, humax⟩ := Finset.exists_max_image _ (wordL G v₁ L L.length) hTne
  obtain ⟨-, huL, hau⟩ := Finset.mem_filter.1 huT
  refine ⟨u, huL, a, ⟨?_, ⟨w', ?_, haw'⟩, ?_⟩, hau, ?_⟩
  · exact List.idxOf_lt_length_of_mem haL
  · rw [List.idxOf_eq_length hw'L]
  · intro a' ha' hex
    obtain ⟨w'', hw'', haw''⟩ := hex
    have ha'L : a' ∈ L := List.idxOf_lt_length_iff.1 ha'
    have hw''L : w'' ∉ L := by
      intro h
      have := List.idxOf_lt_length_of_mem h
      omega
    exact hamax a' (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha'L, w'', hw''L, haw''⟩)
  · intro u' hu' hau'
    have hu'L : u' ∉ L := by
      intro h
      have := List.idxOf_lt_length_of_mem h
      omega
    exact humax u' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu'L, hau'⟩)

theorem build (G : SimpleGraph V) (v₁ : V) (hconn : G.Connected) :
    ∀ m, 1 ≤ m → m ≤ Fintype.card V → ∃ L, ValidL G v₁ L ∧ L.length = m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      refine ⟨[v₁], ⟨List.nodup_singleton v₁, rfl, ?_⟩, rfl⟩
      intro p hp hp0
      have : p < 1 := hp
      omega
    · obtain ⟨L, hv, hlen⟩ := ih hpos (by omega)
      obtain ⟨u, hu, hg⟩ := exists_next G v₁ L hconn hv (by omega)
      exact ⟨L ++ [u], valid_append G v₁ L hv u hu hg, by simp [hlen]⟩

/-- The discovery order read off a list of all vertices. -/
def mkσ (L : List V) (v₁ : V) (h : ∀ x, L.idxOf x < Fintype.card V)
    (hl : ∀ x, L.getD (L.idxOf x) v₁ = x)
    (hr : ∀ j : Fin (Fintype.card V), L.idxOf (L.getD j v₁) = j) :
    V ≃ Fin (Fintype.card V) where
  toFun x := ⟨L.idxOf x, h x⟩
  invFun j := L.getD j v₁
  left_inv x := hl x
  right_inv j := Fin.ext (hr j)

end

end Aux_LexDFS

open TwinWidthI.MinorFree Aux_LexDFS in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (v₁ : V) :
    ∃ (σ : V ≃ Fin (Fintype.card V)) (par : V → V),
      IsLexDFSOrder G σ par ∧ (σ v₁ : ℕ) = 0 := by
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨v₁⟩
  obtain ⟨L, ⟨hnd, hhd, hgood⟩, hlen⟩ := build G v₁ hconn (Fintype.card V) hcard le_rfl
  have hmem : ∀ x, x ∈ L := by
    have h1 : L.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, hlen])
    intro x
    have hx : x ∈ L.toFinset := by rw [h1]; exact Finset.mem_univ x
    exact List.mem_toFinset.1 hx
  have hidx : ∀ x, L.idxOf x < Fintype.card V := by
    intro x
    rw [← hlen]
    exact List.idxOf_lt_length_of_mem (hmem x)
  have hl : ∀ x, L.getD (L.idxOf x) v₁ = x := by
    intro x
    have h1 : L.idxOf x < L.length := List.idxOf_lt_length_of_mem (hmem x)
    rw [List.getD_eq_getElem _ _ h1]
    exact List.getElem_idxOf h1
  have hr : ∀ j : Fin (Fintype.card V), L.idxOf (L.getD j v₁) = j := by
    intro j
    have h1 : (j : ℕ) < L.length := by rw [hlen]; exact j.isLt
    rw [List.getD_eq_getElem _ _ h1]
    exact hnd.idxOf_getElem j h1
  have hgood' : ∀ v, 0 < L.idxOf v → GoodL G v₁ L (L.idxOf v) v := by
    intro v hv
    have h1 : L.idxOf v < L.length := List.idxOf_lt_length_of_mem (hmem v)
    have h2 := hgood (L.idxOf v) h1 hv
    rwa [List.getElem_idxOf h1] at h2
  have hex : ∀ v, ∃ a, (0 < L.idxOf v → ActL G L (L.idxOf v) a ∧ G.Adj a v ∧
      ∀ u, L.idxOf v ≤ L.idxOf u → G.Adj a u →
        wordL G v₁ L (L.idxOf v) u ≤ wordL G v₁ L (L.idxOf v) v) ∧
      (¬ 0 < L.idxOf v → a = v) := by
    intro v
    by_cases hp : 0 < L.idxOf v
    · obtain ⟨a, ha⟩ := hgood' v hp
      exact ⟨a, fun _ => ha, fun h => absurd hp h⟩
    · exact ⟨v, fun h => absurd h hp, fun _ => rfl⟩
  choose par hpar using hex
  refine ⟨mkσ L v₁ hidx hl hr, par, ⟨fun v => ⟨fun h0 => ?_, fun hpos => ?_⟩, ?_⟩, ?_⟩
  · have h0' : L.idxOf v = 0 := h0
    exact (hpar v).2 (by omega)
  · have hpos' : 0 < L.idxOf v := hpos
    obtain ⟨hact, hadj, -⟩ := (hpar v).1 hpos'
    exact ⟨hact, hadj⟩
  · intro v hpos u hle hadj
    have hpos' : 0 < L.idxOf v := hpos
    exact ((hpar v).1 hpos').2.2 u hle hadj
  · obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 hhd
    show L.idxOf v₁ = 0
    rw [ht]
    exact List.idxOf_cons_self
