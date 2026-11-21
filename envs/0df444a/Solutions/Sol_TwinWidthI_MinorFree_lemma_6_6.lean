-- Prove2me | solution 1 for TwinWidthI.MinorFree.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:11:39.773695+00:00
-- url     : https://prove2.me/submissions/8300cee8-5f3c-43e7-98ba-99cfafe26989

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

open TwinWidthI.MinorFree Aux_TWdfs Classical in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ}
    (σ : V ≃ Fin n) (par : V → V) (hdfs : IsDFSOrder G σ par) {k : ℕ}
    (B : Fin k → Set V)
    (hBcons : ∀ j x y z, x ∈ B j → z ∈ B j → σ x ≤ σ y → σ y ≤ σ z → y ∈ B j)
    (hBord : ∀ j j' x y, j < j' → x ∈ B j → y ∈ B j' → σ x < σ y)
    (J : Finset (Fin k)) (v : V) (hv : ∀ j ∈ J, v ∈ MinSubtree par (B j))
    (c : V) (hc : par c = v) (hcv : c ≠ v) :
    (J.filter fun j => ∃ x ∈ MinSubtree par (B j), IsAncestor par c x).card ≤ 2 := by
  have hcpos : 0 < (σ c : ℕ) := by
    by_contra h
    push_neg at h
    have h0 : par c = c := (hdfs c).1 (by omega)
    exact hcv (h0.symm.trans hc)
  have hvc : σ v < σ c := by
    rw [← hc]
    exact par_lt G σ par hdfs c hcpos
  have hsub : (J.filter fun j => ∃ x ∈ MinSubtree par (B j), IsAncestor par c x) ⊆
      J.filter (fun j => c ∈ B j) ∪
        J.filter (fun j => ∃ s ∈ B j, IsAncestor par c s ∧
          ∃ t ∈ B j, ¬ IsAncestor par c t ∧ σ s < σ t) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hjJ, x, hx, hcx⟩ := hj
    obtain ⟨s, hs, s', hs', hxs, -⟩ := hx
    have hcs : IsAncestor par c s := anc_trans par c x s hcx hxs
    obtain ⟨t, ht, t', ht', hvt, hcom⟩ := hv j hjJ
    have hnot : ¬ IsAncestor par c t ∨ ¬ IsAncestor par c t' := by
      by_contra hh
      push_neg at hh
      have hcv' := anc_le G σ par hdfs c v (hcom c hh.1 hh.2)
      exact absurd hvc (not_lt.2 hcv')
    obtain ⟨u, hu, hnu⟩ : ∃ u ∈ B j, ¬ IsAncestor par c u :=
      hnot.elim (fun h => ⟨t, ht, h⟩) (fun h => ⟨t', ht', h⟩)
    have hcs_le : σ c ≤ σ s := anc_le G σ par hdfs c s hcs
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases lt_or_ge (σ u) (σ c) with h1 | h1
    · left
      exact ⟨hjJ, hBcons j u c s hu hs h1.le hcs_le⟩
    · right
      refine ⟨hjJ, s, hs, hcs, u, hu, hnu, ?_⟩
      by_contra h2
      push_neg at h2
      exact hnu (interval G σ par hdfs c u h1 s hcs h2)
  have hA : (J.filter (fun j => c ∈ B j)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro j1 h1 j2 h2
    rw [Finset.mem_filter] at h1 h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact lt_irrefl _ (hBord j1 j2 c c h h1.2 h2.2)
    · exact lt_irrefl _ (hBord j2 j1 c c h h2.2 h1.2)
  have hB : (J.filter (fun j => ∃ s ∈ B j, IsAncestor par c s ∧
      ∃ t ∈ B j, ¬ IsAncestor par c t ∧ σ s < σ t)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro j1 h1 j2 h2
    rw [Finset.mem_filter] at h1 h2
    obtain ⟨-, s1, hs1, hcs1, t1, ht1, hnt1, hst1⟩ := h1
    obtain ⟨-, s2, hs2, hcs2, t2, ht2, hnt2, hst2⟩ := h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h3 := hBord j1 j2 t1 s2 h ht1 hs2
      have hc1 : σ c ≤ σ t1 := le_trans (anc_le G σ par hdfs c s1 hcs1) hst1.le
      exact hnt1 (interval G σ par hdfs c t1 hc1 s2 hcs2 h3.le)
    · have h3 := hBord j2 j1 t2 s1 h ht2 hs1
      have hc2 : σ c ≤ σ t2 := le_trans (anc_le G σ par hdfs c s2 hcs2) hst2.le
      exact hnt2 (interval G σ par hdfs c t2 hc2 s1 hcs1 h3.le)
  calc (J.filter fun j => ∃ x ∈ MinSubtree par (B j), IsAncestor par c x).card
      ≤ (J.filter (fun j => c ∈ B j) ∪
        J.filter (fun j => ∃ s ∈ B j, IsAncestor par c s ∧
          ∃ t ∈ B j, ¬ IsAncestor par c t ∧ σ s < σ t)).card := Finset.card_le_card hsub
    _ ≤ (J.filter (fun j => c ∈ B j)).card +
        (J.filter (fun j => ∃ s ∈ B j, IsAncestor par c s ∧
          ∃ t ∈ B j, ¬ IsAncestor par c t ∧ σ s < σ t)).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega
