-- Prove2me | solution 1 for TwinWidthI.MinorFree.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:15:06.805036+00:00
-- url     : https://prove2.me/submissions/b357626a-b0fe-451e-a8c1-8e686f0851a9

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_LexDFS

namespace Aux_TWdfs
open TwinWidthI.MinorFree

variable {V : Type} [Fintype V] [DecidableEq V]

theorem anc (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) :
    ∀ m : ℕ, ∀ w : V, (σ w : ℕ) = m → ∀ u : V, σ u < σ w →
      (∃ x, (σ w : ℕ) ≤ (σ x : ℕ) ∧ G.Adj u x) → IsAncestor par u w := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw u hu hx
    obtain ⟨x, hx, hux⟩ := hx
    have hu' : (σ u : ℕ) < σ w := hu
    have hpos : 0 < (σ w : ℕ) := lt_of_le_of_lt (Nat.zero_le _) hu'
    obtain ⟨hact, _⟩ := (hdfs w).2 hpos
    obtain ⟨hp_lt, _, hmax⟩ := hact
    have hle : σ u ≤ σ (par w) := hmax u hu' ⟨x, hx, hux⟩
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hup : u = par w := σ.injective heq
      exact ⟨1, by rw [Function.iterate_one, hup]⟩
    · have hx' : (σ (par w) : ℕ) ≤ (σ x : ℕ) := by omega
      obtain ⟨i, hi⟩ := ih (σ (par w) : ℕ) (by omega) (par w) rfl u hlt ⟨x, hx', hux⟩
      exact ⟨i + 1, by rw [Function.iterate_succ_apply, hi]⟩

theorem par_lt (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) (x : V)
    (hx : 0 < (σ x : ℕ)) : σ (par x) < σ x := by
  obtain ⟨hact, _⟩ := (hdfs x).2 hx
  obtain ⟨hp_lt, _, _⟩ := hact
  exact hp_lt

theorem par_le (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) (x : V) :
    σ (par x) ≤ σ x := by
  by_cases h : (σ x : ℕ) = 0
  · rw [(hdfs x).1 h]
  · exact le_of_lt (par_lt G σ par hdfs x (Nat.pos_of_ne_zero h))

theorem anc_le (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) (u w : V)
    (h : IsAncestor par u w) : σ u ≤ σ w := by
  obtain ⟨i, hi⟩ := h
  induction i generalizing w with
  | zero =>
    subst hi
    exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply] at hi
    exact le_trans (ih (par w) hi) (par_le G σ par hdfs w)

theorem anc_trans (par : V → V) (u w z : V)
    (h1 : IsAncestor par u w) (h2 : IsAncestor par w z) : IsAncestor par u z := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := h2
  exact ⟨i + j, by rw [Function.iterate_add_apply, hj, hi]⟩

theorem interval (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) (c y : V)
    (hcy : σ c ≤ σ y) : ∀ x, IsAncestor par c x → σ y ≤ σ x → IsAncestor par c y := by
  intro x hcx
  obtain ⟨m, hm⟩ := hcx
  induction m generalizing x with
  | zero =>
    intro hyx
    have hx : x = c := hm
    rw [hx] at hyx
    have hyc : y = c := σ.injective (le_antisymm hyx hcy)
    rw [hyc]
    exact ⟨0, rfl⟩
  | succ m ih =>
    intro hyx
    have hm' := hm
    rw [Function.iterate_succ_apply] at hm'
    by_cases hyp : σ y ≤ σ (par x)
    · exact ih (par x) hm' hyp
    · push_neg at hyp
      rcases eq_or_lt_of_le hyx with heq | hlt
      · have : y = x := σ.injective heq
        subst this
        exact ⟨m + 1, hm⟩
      · have hxpos : 0 < (σ x : ℕ) := lt_of_le_of_lt (Nat.zero_le _) (show (σ y : ℕ) < σ x from hlt)
        have hadj : G.Adj (par x) x := ((hdfs x).2 hxpos).2
        have h1 : IsAncestor par (par x) y :=
          anc G σ par hdfs (σ y : ℕ) y rfl (par x) hyp ⟨x, le_of_lt hlt, hadj⟩
        exact anc_trans par c (par x) y ⟨m, hm'⟩ h1

end Aux_TWdfs

open TwinWidthI.MinorFree Aux_TWdfs in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) {k : ℕ}
    (a b : Fin k → Fin k → V) (B : Fin k → Set V)
    (hab : ∀ i j, G.Adj (a i j) (b i j))
    (ha : ∀ i j i' j', i < i' → σ (a i j) < σ (a i' j'))
    (hbB : ∀ i j, b i j ∈ B j)
    (hBcons : ∀ j x y z, x ∈ B j → z ∈ B j → σ x ≤ σ y → σ y ≤ σ z → y ∈ B j)
    (hBord : ∀ j j' x y, j < j' → x ∈ B j → y ∈ B j' → σ x < σ y)
    (hAB : ∀ i j j' x, x ∈ B j' → σ (a i j) < σ x) :
    ∀ i j : Fin k, (i : ℕ) + 1 < k → (j : ℕ) + 1 < k →
      Disjoint (MinSubtree par (B j)) (MinSubtree par (Set.range (a i))) := by
  intro i j hi hj
  rw [Set.disjoint_left]
  intro x hx1 hx2
  obtain ⟨s, hs, s', hs', hxs, hcom⟩ := hx1
  obtain ⟨r, hr, r', hr', hxr, -⟩ := hx2
  obtain ⟨j'', rfl⟩ := hr
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin k, (i1 : ℕ) = i + 1 := ⟨⟨i + 1, hi⟩, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ j1 : Fin k, (j1 : ℕ) = j + 1 := ⟨⟨j + 1, hj⟩, rfl⟩
  have hii : i < i1 := by
    show (i : ℕ) < i1
    omega
  have hjj : j < j1 := by
    show (j : ℕ) < j1
    omega
  have hwB : ∀ y ∈ B j, IsAncestor par (a i1 j1) y := fun y hy =>
    anc G σ par hdfs _ y rfl (a i1 j1) (hAB i1 j1 j y hy)
      ⟨b i1 j1, le_of_lt (hBord j j1 y (b i1 j1) hjj hy (hbB i1 j1)), hab i1 j1⟩
  have hwx : IsAncestor par (a i1 j1) x := hcom (a i1 j1) (hwB s hs) (hwB s' hs')
  have h1 : σ (a i1 j1) ≤ σ x := anc_le G σ par hdfs _ _ hwx
  have h2 : σ x ≤ σ (a i j'') := anc_le G σ par hdfs _ _ hxr
  have h3 : σ (a i j'') < σ (a i1 j1) := ha i j'' i1 j1 hii
  exact lt_irrefl _ (lt_of_lt_of_le h3 (h1.trans h2))
