-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @yammering
-- created : 2026-10-09T03:07:52.179372+00:00
-- url     : https://prove2.me/submissions/1df8da6d-1dbe-4bac-b0fc-d34e297bc610

import Mathlib

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Connectivity inside a vertex set, and the complement of a pair -/

/-- `ConnSub G S`: any two vertices of `S` are joined by a `G`-walk whose
support stays inside `S`. -/
def lemma10_ConnSub (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ w : G.Walk x y, ∀ z ∈ w.support, z ∈ S

/-- The complement of a pair, as a finset. -/
def lemma10_complPair (x y : V) : Finset V :=
  (Finset.univ.erase x).erase y

lemma lemma10_mem_complPair (x y z : V) :
    z ∈ lemma10_complPair x y ↔ z ≠ x ∧ z ≠ y := by
  simp only [lemma10_complPair, Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

lemma lemma10_card_complPair (x y : V) (hxy : x ≠ y) :
    #(lemma10_complPair x y) = #(Finset.univ : Finset V) - 2 := by
  have h1 : #((Finset.univ.erase x : Finset V)) + 1 =
      #(Finset.univ : Finset V) :=
    Finset.card_erase_add_one (Finset.mem_univ x)
  have h2mem : y ∈ (Finset.univ.erase x : Finset V) := by
    rw [Finset.mem_erase]
    exact ⟨hxy.symm, Finset.mem_univ y⟩
  have h2 : #(lemma10_complPair x y) + 1 =
      #((Finset.univ.erase x : Finset V)) := by
    unfold lemma10_complPair
    exact Finset.card_erase_add_one h2mem
  omega

/-! ## Crossing edge out of a set -/

/-- Cons case of `lemma10_aux_adj`, with the middle vertex named explicitly. -/
lemma lemma10_aux_adj_step (G : SimpleGraph V) {S : Finset V} {x mid y : V}
    (h : G.Adj x mid) (t : G.Walk mid y) (hx : x ∈ S) (hy : y ∉ S)
    (ih : mid ∈ S → y ∉ S → ∃ z, z ∉ S ∧ ∃ u, u ∈ S ∧ G.Adj u z) :
    ∃ z, z ∉ S ∧ ∃ u, u ∈ S ∧ G.Adj u z := by
  by_cases hx' : mid ∈ S
  · exact ih hx' hy
  · exact ⟨_, hx', _, hx, h⟩

/-- From a walk leaving `S`, extract an edge crossing out of `S`. -/
lemma lemma10_aux_adj (G : SimpleGraph V) {S : Finset V} {x y : V}
    (q : G.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ z, z ∉ S ∧ ∃ u, u ∈ S ∧ G.Adj u z := by
  revert hx hy
  induction q with
  | nil => intro hx hy; exact (hy hx).elim
  | cons h t ih =>
    intro hx hy
    exact lemma10_aux_adj_step G h t hx hy ih

/-! ## At least three vertices -/

/-- Minimum degree two forces at least three vertices. -/
lemma lemma10_card_univ_ge_three (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hdeg : ∀ v, 2 ≤ G.degree v) : 3 ≤ #(Finset.univ : Finset V) := by
  obtain ⟨v₀⟩ := hG.nonempty
  have h2v : 2 ≤ #(G.neighborFinset v₀) := hdeg v₀
  obtain ⟨n₁, hn₁, n₂, hn₂, hne⟩ :=
    (Finset.one_lt_card.mp (by omega : 1 < #(G.neighborFinset v₀)))
  have hn₁v : n₁ ≠ v₀ := by
    have h : G.Adj v₀ n₁ := by rwa [G.mem_neighborFinset] at hn₁
    exact h.ne.symm
  have hn₂v : n₂ ≠ v₀ := by
    have h : G.Adj v₀ n₂ := by rwa [G.mem_neighborFinset] at hn₂
    exact h.ne.symm
  have h3 : #({v₀, n₁, n₂} : Finset V) = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · rw [Finset.mem_singleton]
      exact hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hn₁v.symm, hn₂v.symm⟩
  have hle := Finset.card_le_card (Finset.subset_univ ({v₀, n₁, n₂} : Finset V))
  omega

/-! ## Singleton and join -/

lemma lemma10_connSub_singleton (G : SimpleGraph V) (w : V) :
    lemma10_ConnSub G {w} := by
  intro x hx y hy
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]
  refine ⟨Walk.nil, ?_⟩
  intro z hz
  rw [Walk.mem_support_nil_iff] at hz
  rw [hz]
  exact Finset.mem_singleton_self w

/-- Attach a vertex adjacent to `S`: connectivity extends to the insert. -/
lemma lemma10_join (G : SimpleGraph V) (S : Finset V)
    (hS : lemma10_ConnSub G S) (t : V) (ht : t ∉ S) (s₀ : V)
    (hs₀ : s₀ ∈ S) (hadj : G.Adj t s₀) :
    lemma10_ConnSub G (insert t S) := by
  intro x hx y hy
  rw [Finset.mem_insert] at hx hy
  rcases hx with heqx | hx <;> rcases hy with heqy | hy
  · rw [heqx, heqy]
    refine ⟨Walk.nil, ?_⟩
    intro z hz
    rw [Walk.mem_support_nil_iff] at hz
    rw [hz]
    exact Finset.mem_insert_self t S
  · rw [heqx]
    obtain ⟨wold, hwold⟩ := hS s₀ hs₀ y hy
    refine ⟨hadj.toWalk.append wold, ?_⟩
    intro z hz
    rw [Walk.support_append] at hz
    rcases List.mem_append.mp hz with h1 | h1
    · rw [SimpleGraph.Adj.support_toWalk] at h1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with heq | heq <;> rw [heq]
      · exact Finset.mem_insert_self t S
      · exact Finset.mem_insert_of_mem hs₀
    · exact Finset.mem_insert_of_mem (hwold z (List.mem_of_mem_tail h1))
  · rw [heqy]
    obtain ⟨wold, hwold⟩ := hS x hx s₀ hs₀
    refine ⟨wold.append hadj.toWalk.reverse, ?_⟩
    intro z hz
    rw [Walk.support_append] at hz
    rcases List.mem_append.mp hz with h1 | h1
    · exact Finset.mem_insert_of_mem (hwold z h1)
    · have h2 : z ∈ hadj.toWalk.reverse.support := List.mem_of_mem_tail h1
      rw [Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Adj.support_toWalk] at h2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
      rcases h2 with heq | heq <;> rw [heq]
      · exact Finset.mem_insert_self t S
      · exact Finset.mem_insert_of_mem hs₀
  · obtain ⟨wold, hwold⟩ := hS x hx y hy
    exact ⟨wold, fun z hq => Finset.mem_insert_of_mem (hwold z hq)⟩

/-! ## Lifting walks into an induced subgraph -/

/-- A walk supported in `S` lifts to a walk in the induced subgraph. -/
noncomputable def lemma10_lift (G : SimpleGraph V) (S : Finset V) {x y : V}
    (w : G.Walk x y) (hx : x ∈ S) (hy : y ∈ S)
    (hsup : ∀ z ∈ w.support, z ∈ S) :
    (G.induce (↑S : Set V)).Walk ⟨x, Finset.mem_coe.mpr hx⟩
      ⟨y, Finset.mem_coe.mpr hy⟩ := by
  revert hx hy hsup
  induction w with
  | nil => intro hx hy hsup; exact Walk.nil
  | cons h t ih =>
    intro hx hy hsup
    have hsup' : ∀ z ∈ t.support, z ∈ S := fun z hz =>
      hsup z (by simp [Walk.support_cons, hz])
    have hmid : _ ∈ S := hsup' _ t.start_mem_support
    exact Walk.cons (SimpleGraph.induce_adj.mpr h)
      (ih hmid hy hsup')

/-! ## The maximality step: a bigger candidate is impossible -/

/-- Attaching `t` to `K` for a new edge gives a strictly bigger candidate,
contradicting maximality. -/
lemma lemma10_bigger (G : SimpleGraph V) (K : Finset V)
    (hKconn : lemma10_ConnSub G K)
    (hmax : ∀ a b K', G.Adj a b → K' ⊆ lemma10_complPair a b →
      lemma10_ConnSub G K' → #K' ≤ #K)
    (a b t : V) (hab : G.Adj a b) (htK : t ∉ K) (hta : t ≠ a)
    (htb : t ≠ b) (hKa : ∀ z ∈ K, z ≠ a) (hKb : ∀ z ∈ K, z ≠ b)
    (s₀ : V) (hs₀ : s₀ ∈ K) (hadj : G.Adj t s₀) : False := by
  have hconn2 := lemma10_join G K hKconn t htK s₀ hs₀ hadj
  have hsub2 : insert t K ⊆ lemma10_complPair a b := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rw [lemma10_mem_complPair]
    rcases hz with heq | hz
    · rw [heq]; exact ⟨hta, htb⟩
    · exact ⟨hKa z hz, hKb z hz⟩
  have hle := hmax a b (insert t K) hab hsub2 hconn2
  rw [Finset.card_insert_of_notMem htK] at hle
  omega

/-- From membership and non-membership, inequality. -/
lemma lemma10_ne_of_mem_of_not_mem {S : Finset V} {a b : V} (ha : a ∈ S)
    (hb : b ∉ S) : a ≠ b := by
  intro heq
  subst heq
  exact hb ha

/-! ## The maximality argument -/

/-- Core: some edge has its complement connected (in the `ConnSub` sense). -/
lemma lemma10_core (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∃ a b, G.Adj a b ∧ lemma10_ConnSub G (lemma10_complPair a b) := by
  -- A largest connected subset over all removed edges.
  have hex : ∃ x y K, G.Adj x y ∧ K ⊆ lemma10_complPair x y ∧
      lemma10_ConnSub G K ∧ 1 ≤ #K ∧
      ∀ a b K', G.Adj a b → K' ⊆ lemma10_complPair a b →
        lemma10_ConnSub G K' → #K' ≤ #K := by
    obtain ⟨v₀⟩ := hG.nonempty
    have h2v : 2 ≤ #(G.neighborFinset v₀) := hdeg v₀
    obtain ⟨u, hu⟩ :=
      Finset.card_pos.mp (show 0 < #(G.neighborFinset v₀) by omega)
    have hadjvu : G.Adj v₀ u := by rwa [G.mem_neighborFinset] at hu
    have hV3 : 3 ≤ #(Finset.univ : Finset V) :=
      lemma10_card_univ_ge_three G hG hdeg
    have hS₀card : 1 ≤ #(lemma10_complPair v₀ u) := by
      have h := lemma10_card_complPair v₀ u hadjvu.ne
      omega
    obtain ⟨w, hw⟩ :=
      Finset.card_pos.mp (show 0 < #(lemma10_complPair v₀ u) by omega)
    have hconw : lemma10_ConnSub G {w} := lemma10_connSub_singleton G w
    have hwsub : ({w} : Finset V) ⊆ lemma10_complPair v₀ u :=
      Finset.singleton_subset_iff.mpr hw
    classical
    set Cands : Finset ((V × V) × Finset V) :=
      ((Finset.univ.product Finset.univ).product Finset.univ.powerset).filter
        (fun p => G.Adj p.1.1 p.1.2 ∧
          p.2 ⊆ lemma10_complPair p.1.1 p.1.2 ∧ lemma10_ConnSub G p.2) with hC
    have hmem : ((v₀, u), {w}) ∈ Cands := by
      rw [hC, Finset.mem_filter]
      exact ⟨by simp, hadjvu, hwsub, hconw⟩
    have hne : Cands.Nonempty := ⟨_, hmem⟩
    obtain ⟨p, hpS, hmax⟩ :=
      Finset.exists_max_image Cands (fun p => #(p.2)) hne
    obtain ⟨⟨x, y⟩, K⟩ := p
    rw [hC, Finset.mem_filter] at hpS
    obtain ⟨-, hadj, hsub, hconn⟩ := hpS
    have hK1 : 1 ≤ #K := by
      have hle : #(({w} : Finset V)) ≤ #K := hmax _ hmem
      rwa [Finset.card_singleton] at hle
    refine ⟨x, y, K, hadj, hsub, hconn, hK1, ?_⟩
    intro a b K' hadj' hsub' hconn'
    have hmem' : ((a, b), K') ∈ Cands := by
      rw [hC, Finset.mem_filter]
      exact ⟨by simp, hadj', hsub', hconn'⟩
    exact hmax _ hmem'
  obtain ⟨x, y, K, hxy, hKsub, hKconn, hK1, hmax⟩ := hex
  set R := lemma10_complPair x y \ K with hR
  have hRsub : R ⊆ lemma10_complPair x y := by
    rw [hR]
    exact Finset.sdiff_subset
  have hRmem : ∀ z : V, z ∈ R ↔
      z ∈ lemma10_complPair x y ∧ z ∉ K := by
    intro z
    rw [hR, Finset.mem_sdiff]
  have hxK : x ∉ K := fun hh =>
    ((lemma10_mem_complPair x y x).mp (hKsub hh)).1 rfl
  have hyK : y ∉ K := fun hh =>
    ((lemma10_mem_complPair x y y).mp (hKsub hh)).2 rfl
  have hxR : x ∉ R := fun hh =>
    ((lemma10_mem_complPair x y x).mp (hRsub hh)).1 rfl
  have hyR : y ∉ R := fun hh =>
    ((lemma10_mem_complPair x y y).mp (hRsub hh)).2 rfl
  have hxyne : x ≠ y := hxy.ne
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  -- No edges between K and R, else K would not be largest.
  have noRK : ∀ k ∈ K, ∀ r ∈ R, ¬ G.Adj k r := by
    intro k hk r hr hadj
    have hrC : r ∈ lemma10_complPair x y := ((hRmem r).mp hr).1
    have hrK : r ∉ K := ((hRmem r).mp hr).2
    have hconn2 := lemma10_join G K hKconn r hrK k hk hadj.symm
    have hsub2 : insert r K ⊆ lemma10_complPair x y := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with heq | hz
      · rw [heq]; exact hrC
      · exact hKsub hz
    have hle := hmax x y (insert r K) hxy hsub2 hconn2
    rw [Finset.card_insert_of_notMem hrK] at hle
    omega
  -- K touches the removed pair.
  obtain ⟨k₀, hk₀⟩ := hKne
  have step3 : ∃ k ∈ K, (G.Adj k x ∨ G.Adj k y) := by
    obtain ⟨w⟩ := hG k₀ x
    obtain ⟨z, hzK, u, huK, hadj⟩ := lemma10_aux_adj G w hk₀ hxK
    have hzE : z = x ∨ z = y := by
      by_contra hcon
      push_neg at hcon
      have hzC : z ∈ lemma10_complPair x y :=
        (lemma10_mem_complPair x y z).mpr ⟨hcon.1, hcon.2⟩
      by_cases hzR : z ∈ R
      · exact (noRK u huK z hzR hadj).elim
      · have hzR' : z ∈ R := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨hzC, hzK⟩
        exact hzR hzR'
    rcases hzE with heq | heq
    · refine ⟨u, huK, Or.inl ?_⟩; rwa [← heq]
    · refine ⟨u, huK, Or.inr ?_⟩; rwa [← heq]
  -- Split on whether anything remains outside K.
  by_cases hRne : R.Nonempty
  · -- R nonempty: derive a contradiction via case analysis.
    exfalso
    obtain ⟨r₀, hr₀⟩ := hRne
    -- R touches the removed pair.
    have step5 : ∃ u ∈ R, (G.Adj u x ∨ G.Adj u y) := by
      obtain ⟨w⟩ := hG r₀ k₀
      have hk₀R : k₀ ∉ R := by
        rw [hR, Finset.mem_sdiff]
        intro hcon
        exact hcon.2 hk₀
      obtain ⟨z, hzR, u, huR, hadj⟩ := lemma10_aux_adj G w hr₀ hk₀R
      have hzE : z = x ∨ z = y := by
        by_contra hcon
        push_neg at hcon
        have hzC : z ∈ lemma10_complPair x y :=
          (lemma10_mem_complPair x y z).mpr ⟨hcon.1, hcon.2⟩
        by_cases hzK : z ∈ K
        · exact (noRK z hzK u huR hadj.symm).elim
        · have hzR' : z ∈ R := by
            rw [hR]
            exact Finset.mem_sdiff.mpr ⟨hzC, hzK⟩
          exact hzR hzR'
      rcases hzE with heq | heq
      · refine ⟨u, huR, Or.inl ?_⟩; rwa [← heq]
      · refine ⟨u, huR, Or.inr ?_⟩; rwa [← heq]
    -- Case A/B: does y touch K?
    by_cases hAy : ∃ k ∈ K, G.Adj y k
    · -- Case A.
      obtain ⟨ky, hky, hadjy⟩ := hAy
      by_cases hRx : ∃ r ∈ R, G.Adj r x
      · -- A1: join y over edge (r, x).
        obtain ⟨r, hr, hrx⟩ := hRx
        have hrK : r ∉ K := ((hRmem r).mp hr).2
        exact lemma10_bigger G K hKconn hmax r x y hrx hyK
          ((lemma10_ne_of_mem_of_not_mem hr hyR).symm) hxyne.symm
          (fun z hz => lemma10_ne_of_mem_of_not_mem hz hrK)
          (fun z hz => lemma10_ne_of_mem_of_not_mem hz hxK)
          ky hky hadjy
      · -- A2: no vertex of R touches x.
        by_cases hxK' : ∃ k ∈ K, G.Adj x k
        · -- A2a: join x over edge (y, u).
          obtain ⟨kx, hkx, hadjx⟩ := hxK'
          obtain ⟨u, huR, huxy⟩ := step5
          have hadjyu : G.Adj y u := by
            rcases huxy with hux | huy
            · exact absurd ⟨u, huR, hux⟩ hRx
            · exact huy.symm
          have huK : u ∉ K := ((hRmem u).mp huR).2
          exact lemma10_bigger G K hKconn hmax y u x hadjyu hxK hxyne
            ((lemma10_ne_of_mem_of_not_mem huR hxR).symm)
            (fun z hz => lemma10_ne_of_mem_of_not_mem hz hyK)
            (fun z hz => lemma10_ne_of_mem_of_not_mem hz huK)
            kx hkx hadjx
        · -- A2b: x would have degree at most one.
          have hsub : G.neighborFinset x ⊆ {y} := by
            intro z hz
            have hadjxz : G.Adj x z := by rwa [G.mem_neighborFinset] at hz
            by_cases hzK : z ∈ K
            · exact absurd ⟨z, hzK, hadjxz⟩ hxK'
            · by_cases hzR : z ∈ R
              · exact absurd ⟨z, hzR, hadjxz.symm⟩ hRx
              · have hzE : z = x ∨ z = y := by
                  by_contra hcon
                  push_neg at hcon
                  have hzC : z ∈ lemma10_complPair x y :=
                    (lemma10_mem_complPair x y z).mpr ⟨hcon.1, hcon.2⟩
                  by_cases hzK' : z ∈ K
                  · exact hzK hzK'
                  · have hzR' : z ∈ R := by
                      rw [hR]
                      exact Finset.mem_sdiff.mpr ⟨hzC, hzK'⟩
                    exact hzR hzR'
                rcases hzE with heq | heq
                · exact absurd heq hadjxz.ne.symm
                · rw [heq]
                  exact Finset.mem_singleton_self y
          have hle1 : #(G.neighborFinset x) ≤ 1 := by
            have h2 := Finset.card_le_card hsub
            rw [Finset.card_singleton] at h2
            exact h2
          have h2x : 2 ≤ #(G.neighborFinset x) := hdeg x
          omega
    · -- Case B: y does not touch K, so x must.
      have hxK' : ∃ k ∈ K, G.Adj x k := by
        obtain ⟨k, hk, hkx | hky⟩ := step3
        · exact ⟨k, hk, hkx.symm⟩
        · exact absurd ⟨k, hk, hky.symm⟩ hAy
      obtain ⟨kx, hkx, hadjx⟩ := hxK'
      by_cases hRx : ∃ r ∈ R, G.Adj r x
      · -- B1.
        obtain ⟨r, hr, hrx⟩ := hRx
        by_cases hRe : ∃ a ∈ R, ∃ b ∈ R, G.Adj a b
        · -- B1 with an R-edge: join x over it.
          obtain ⟨a, haR, b, hbR, hab⟩ := hRe
          have haK : a ∉ K := ((hRmem a).mp haR).2
          have hbK : b ∉ K := ((hRmem b).mp hbR).2
          exact lemma10_bigger G K hKconn hmax a b x hab hxK
            ((lemma10_ne_of_mem_of_not_mem haR hxR).symm)
            ((lemma10_ne_of_mem_of_not_mem hbR hxR).symm)
            (fun z hz => lemma10_ne_of_mem_of_not_mem hz haK)
            (fun z hz => lemma10_ne_of_mem_of_not_mem hz hbK)
            kx hkx hadjx
        · -- B1 singleton case: every R vertex sees exactly {x, y}.
          have hrK : r ∉ K := ((hRmem r).mp hr).2
          have hNr : G.neighborFinset r = {x, y} := by
            refine Finset.eq_of_subset_of_card_le ?_ ?_
            · intro z hz
              have hadjrz : G.Adj r z := by rwa [G.mem_neighborFinset] at hz
              by_cases hzK : z ∈ K
              · exact absurd hadjrz.symm (noRK z hzK r hr)
              · by_cases hzR : z ∈ R
                · exact absurd ⟨r, hr, z, hzR, hadjrz⟩ hRe
                · have hzE : z = x ∨ z = y := by
                    by_contra hcon
                    push_neg at hcon
                    have hzC : z ∈ lemma10_complPair x y :=
                      (lemma10_mem_complPair x y z).mpr ⟨hcon.1, hcon.2⟩
                    by_cases hzK' : z ∈ K
                    · exact hzK hzK'
                    · have hzR' : z ∈ R := by
                        rw [hR]
                        exact Finset.mem_sdiff.mpr ⟨hzC, hzK'⟩
                      exact hzR hzR'
                  rw [Finset.mem_insert, Finset.mem_singleton]
                  exact hzE
            · have hmem : x ∉ ({y} : Finset V) := by
                rw [Finset.mem_singleton]
                exact hxyne
              have h2xy : #(({x, y} : Finset V)) = 2 := by
                rw [Finset.card_insert_of_notMem hmem, Finset.card_singleton]
              have h2r : 2 ≤ #(G.neighborFinset r) := hdeg r
              omega
          have hry : G.Adj r y := by
            have hy : y ∈ G.neighborFinset r := by
              rw [hNr]
              exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
            rwa [G.mem_neighborFinset] at hy
          exact lemma10_bigger G K hKconn hmax y r x hry.symm hxK hxyne
            ((lemma10_ne_of_mem_of_not_mem hr hxR).symm)
            (fun z hz => lemma10_ne_of_mem_of_not_mem hz hyK)
            (fun z hz => lemma10_ne_of_mem_of_not_mem hz hrK)
            kx hkx hadjx
      · -- B2: R touches y; join x over (y, u).
        obtain ⟨u, huR, huxy⟩ := step5
        have hadjyu : G.Adj y u := by
          rcases huxy with hux | huy
          · exact absurd ⟨u, huR, hux⟩ hRx
          · exact huy.symm
        have huK : u ∉ K := ((hRmem u).mp huR).2
        exact lemma10_bigger G K hKconn hmax y u x hadjyu hxK hxyne
          ((lemma10_ne_of_mem_of_not_mem huR hxR).symm)
          (fun z hz => lemma10_ne_of_mem_of_not_mem hz hyK)
          (fun z hz => lemma10_ne_of_mem_of_not_mem hz huK)
          kx hkx hadjx
  · -- R is empty: K is the whole complement.
    have hRem : R = ∅ := by
      ext z
      simp only [Finset.notMem_empty, iff_false]
      intro hz
      exact hRne ⟨z, hz⟩
    have hKR : K = lemma10_complPair x y := by
      apply le_antisymm hKsub
      intro z hz
      by_contra hzK
      have hzR : z ∈ R := by
        rw [hR]
        exact Finset.mem_sdiff.mpr ⟨hz, hzK⟩
      rw [hRem] at hzR
      exact Finset.notMem_empty z hzR
    refine ⟨x, y, hxy, ?_⟩
    rwa [← hKR]

/-! ## Main theorem -/

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∃ x y : V, G.Adj x y ∧ (G.induce ({x, y}ᶜ : Set V)).Connected := by
  obtain ⟨a, b, hadj, hconn⟩ := lemma10_core G hG hdeg
  refine ⟨a, b, hadj, ?_⟩
  have hSeq : (↑(lemma10_complPair a b) : Set V) = ({a, b} : Set V)ᶜ := by
    ext z
    simp only [Finset.mem_coe, lemma10_mem_complPair, Set.mem_compl_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [← hSeq]
  have hcard : 1 ≤ #(lemma10_complPair a b) := by
    have h3 := lemma10_card_univ_ge_three G hG hdeg
    have h := lemma10_card_complPair a b hadj.ne
    omega
  obtain ⟨x₀, hx₀⟩ :=
    Finset.card_pos.mp (show 0 < #(lemma10_complPair a b) by omega)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x₀, Finset.mem_coe.mpr hx₀⟩, fun y => ?_⟩
  obtain ⟨w, hw⟩ := hconn x₀ hx₀ y.1 (Finset.mem_coe.mp y.2)
  exact ⟨lemma10_lift G _ w hx₀ (Finset.mem_coe.mp y.2) hw⟩
