-- Prove2me | solution 1 for OneTwoThree.Weighting.lemma_5_parity_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-12T13:22:06.830009+00:00
-- url     : https://prove2.me/submissions/65f8dc01-f949-4dbd-aed6-c8ea4c5cdf8f

import Mathlib

set_option autoImplicit false

/-- Parity toggle for the symmetric difference of two edge sets, at the level of
    incidence counts at a single vertex: the incidence of `J \ P ∪ (P \ J)` at `v`
    is odd iff exactly one of the incidences of `J`, `P` at `v` is odd. -/
lemma tjoin_odd_incidence_symmDiff {V : Type*} [DecidableEq V] (J P : Finset (Sym2 V))
    (v : V) :
    Odd (Finset.card ((J \ P ∪ (P \ J)).filter (fun e => v ∈ e))) ↔
      (Odd (Finset.card (J.filter (fun e => v ∈ e))) ↔
        ¬ Odd (Finset.card (P.filter (fun e => v ∈ e)))) := by
  have hdisj : Disjoint ((J \ P).filter (fun e => v ∈ e))
      ((P \ J).filter (fun e => v ∈ e)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [Finset.mem_filter] at he1 he2
    exact (Finset.mem_sdiff.mp he1.1).2 (Finset.mem_sdiff.mp he2.1).1
  have hJ : (J \ P).filter (fun e => v ∈ e) = (J.filter (fun e => v ∈ e)) \ P := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hP : (P \ J).filter (fun e => v ∈ e) = (P.filter (fun e => v ∈ e)) \ J := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hinter : P ∩ (J.filter (fun e => v ∈ e)) = J ∩ (P.filter (fun e => v ∈ e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  rw [Finset.filter_union, Finset.card_union_of_disjoint hdisj, hJ, hP,
    Finset.card_sdiff, Finset.card_sdiff, hinter]
  have hsub1 : J ∩ (P.filter (fun e => v ∈ e)) ⊆ J.filter (fun e => v ∈ e) := by
    intro e he
    rw [Finset.mem_inter] at he
    rw [Finset.mem_filter]
    exact ⟨he.1, (Finset.mem_filter.mp he.2).2⟩
  have hsub2 : J ∩ (P.filter (fun e => v ∈ e)) ⊆ P.filter (fun e => v ∈ e) :=
    Finset.inter_subset_right
  have h1 := Finset.card_le_card hsub1
  have h2 := Finset.card_le_card hsub2
  simp only [Nat.odd_iff]
  omega

/-- A walk from `u` to `w` yields an edge set whose odd-incidence vertices are
    exactly `{u} △ {w}` (i.e. `u` xor `w`), by symmetric-difference toggling
    along the walk. -/
lemma tjoin_walk_odd_incidence {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ∀ {u w : V} (p : G.Walk u w),
    ∃ P : Finset (Sym2 V), (P : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ∀ v, Odd (Finset.card (P.filter (fun e => v ∈ e))) ↔
        ((v = u) ↔ ¬ (v = w)) := by
  intro u w p
  induction p with
  | nil =>
      refine ⟨∅, by simp, fun v => ?_⟩
      simp only [Finset.filter_empty, Finset.card_empty]
      rw [show (Odd (0 : ℕ)) ↔ False from
        ⟨fun h => by obtain ⟨m, hm⟩ := h; omega, fun h => h.elim⟩]
      exact iff_of_false not_false iff_not_self
  | cons hadj p ih =>
      rename_i u x w
      obtain ⟨P, hPsub, hP⟩ := ih
      have hne : u ≠ x := G.ne_of_adj hadj
      have hedge : s(u, x) ∈ G.edgeSet := G.mem_edgeSet.mpr hadj
      refine ⟨(P \ {s(u, x)}) ∪ ({s(u, x)} \ P), ?_, fun v => ?_⟩
      · intro e he
        rw [Finset.coe_union, Set.mem_union] at he
        rcases he with h | h
        · rw [Finset.coe_sdiff, Set.mem_sdiff] at h
          exact hPsub h.1
        · rw [Finset.coe_sdiff, Set.mem_sdiff] at h
          rw [Finset.coe_singleton, Set.mem_singleton_iff] at h
          rw [h.1]
          exact hedge
      · have htog := tjoin_odd_incidence_symmDiff P {s(u, x)} v
        rw [hP v] at htog
        have hmem : v ∈ s(u, x) ↔ (v = u ∨ v = x) := Sym2.mem_iff
        have hsing : Odd (Finset.card (({s(u, x)} : Finset (Sym2 V)).filter (fun e => v ∈ e))) ↔
            (v = u ∨ v = x) := by
          rw [Finset.filter_singleton]
          by_cases hv : v ∈ s(u, x)
          · rw [if_pos hv, Finset.card_singleton]
            exact iff_of_true ⟨0, rfl⟩ (hmem.mp hv)
          · rw [if_neg hv, Finset.card_empty]
            rw [show (Odd (0 : ℕ)) ↔ False from
              ⟨fun h => by obtain ⟨m, hm⟩ := h; omega, fun h => h.elim⟩]
            exact iff_of_false not_false (fun hcon => hv (hmem.mpr hcon))
        rw [hsing] at htog
        refine htog.trans ?_
        have hbc : (v = u) → (v = x) → False := fun h1 h2 => hne (h1.symm.trans h2)
        tauto

/-- T-join existence: induction on `k` where `Even (card s)` unfolds to
    `card s = k + k`. Each step removes two vertices joined by a walk and
    toggles the inductively obtained edge set along that walk's edges. -/
lemma tjoin_exists {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) : ∀ k : ℕ, ∀ s : Finset V, Finset.card s = k + k →
    ∃ E_o : Finset (Sym2 V), (E_o : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔ v ∈ s := by
  intro k
  induction k with
  | zero =>
      intro s hs
      have hempty : s = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hempty
      refine ⟨∅, by simp, fun v => ?_⟩
      simp only [Finset.filter_empty, Finset.card_empty, Finset.notMem_empty]
      rw [show (Odd (0 : ℕ)) ↔ False from
        ⟨fun h => by obtain ⟨m, hm⟩ := h; omega, fun h => h.elim⟩]
  | succ k ih =>
      intro s hs
      have hcard : 2 ≤ Finset.card s := by omega
      have hne : s.Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨u, hu⟩ := hne
      have hcard1 : Finset.card (s.erase u) = Finset.card s - 1 :=
        Finset.card_erase_of_mem hu
      have hne1 : (s.erase u).Nonempty := by
        rw [← Finset.card_pos, hcard1]
        omega
      obtain ⟨w, hw⟩ := hne1
      rw [Finset.mem_erase] at hw
      obtain ⟨hwu, hws⟩ := hw
      have hs' : Finset.card ((s.erase u).erase w) = k + k := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwu, hws⟩), hcard1]
        omega
      obtain ⟨P', hP'sub, hP'⟩ := ih ((s.erase u).erase w) hs'
      obtain ⟨p⟩ := hG u w
      obtain ⟨Q, hQsub, hQ⟩ := tjoin_walk_odd_incidence G p
      refine ⟨(P' \ Q) ∪ (Q \ P'), ?_, fun v => ?_⟩
      · intro e he
        rw [Finset.coe_union, Set.mem_union] at he
        rcases he with h | h
        · rw [Finset.coe_sdiff, Set.mem_sdiff] at h
          exact hP'sub h.1
        · rw [Finset.coe_sdiff, Set.mem_sdiff] at h
          exact hQsub h.1
      · have htog := tjoin_odd_incidence_symmDiff P' Q v
        rw [hP' v, hQ v] at htog
        refine htog.trans ?_
        have hmem : v ∈ (s.erase u).erase w ↔ (v ∈ s ∧ v ≠ u ∧ v ≠ w) := by
          rw [Finset.mem_erase, Finset.mem_erase]
          tauto
        rw [hmem]
        have hbu : (v = u) → (v ∈ s) := by
          intro h
          rw [h]
          exact hu
        have hcw : (v = w) → (v ∈ s) := by
          intro h
          rw [h]
          exact hws
        have hbc : (v = u) → (v = w) → False := fun h1 h2 => hwu (h1.symm.trans h2).symm
        by_cases hB : v = u <;> by_cases hC : v = w
        · exact (hbc hB hC).elim
        · subst hB
          have hmem : v ∈ s := hbu rfl
          simp [hC, hmem]
        · subst hC
          have hmem : v ∈ s := hcw rfl
          simp [hB, hmem]
        · simp [hB, hC]

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (V_o : Finset V) (heven : Even (Finset.card V_o)) :
    ∃ E_o : Finset (Sym2 V),
      (E_o : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔ v ∈ V_o := by
  obtain ⟨k, hk⟩ := heven
  exact tjoin_exists G hG k V_o hk

/-- Alias under the published node name: the platform verifier looks up the
    published theorem name in the submission environment (dual-naming recipe). -/
theorem OneTwoThree.Weighting.lemma_5_parity_subgraph {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (V_o : Finset V) (heven : Even (Finset.card V_o)) :
    ∃ E_o : Finset (Sym2 V),
      (E_o : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔ v ∈ V_o :=
  solution G hG V_o heven
