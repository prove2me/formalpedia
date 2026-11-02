-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:13:13.865357+00:00
-- url     : https://prove2.me/submissions/b5104cf5-69dc-4715-b3b9-6fff2a0420d8

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hconnected : ∀ s ∈ C, (N.induce (s : Set V)).Connected)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  have hdisj : (C : Set (Finset V)).PairwiseDisjoint id := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro v hvs hvt
    obtain ⟨u, hu, huniq⟩ := hpartition v
    have hsu : s = u := huniq s ⟨hs, hvs⟩
    have htu : t = u := huniq t ⟨ht, hvt⟩
    exact hst (hsu.trans htu.symm)
  have hcover : ∀ v : V, ∃ s, s ∈ C ∧ v ∈ s := by
    intro v
    obtain ⟨s, ⟨hs, hv⟩, _⟩ := hpartition v
    exact ⟨s, hs, hv⟩
  have hunion : C.biUnion id = Finset.univ := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, id_eq, iff_true]
    exact hcover v
  have hsum : (∑ s ∈ C, s.card) = Fintype.card V := by
    calc
      (∑ s ∈ C, s.card) = (C.biUnion id).card := (Finset.card_biUnion hdisj).symm
      _ = Fintype.card V := by rw [hunion]; simp
  have hslack : ∀ s ∈ C,
      (N.induce (s : Set V)).edgeFinset.card + 3 <= 3 * s.card := by
    intro s hs
    by_cases hthree : 3 <= s.card
    · have hb := hlocal s hthree (hconnected s hs)
      have hsix : 6 <= 3 * s.card := by omega
      have hb' : (N.induce (s : Set V)).edgeFinset.card + 6 <= 3 * s.card :=
        (Nat.le_sub_iff_add_le hsix).mp hb
      omega
    · have hsmall : s.card <= 2 := by omega
      have he := (N.induce (s : Set V)).card_edgeFinset_le_card_choose_two
      have hsubcard : Fintype.card (s : Set V) = s.card := by simp
      rw [hsubcard] at he
      interval_cases hsz : s.card
      · have : s.card > 0 := Finset.card_pos.mpr (hnonempty s hs)
        omega
      · have he0 : (N.induce (s : Set V)).edgeFinset.card <= 0 := by
          simpa [hsz] using he
        omega
      · have he1 : (N.induce (s : Set V)).edgeFinset.card <= 1 := by
          simpa [hsz] using he
        omega
  have htotal : N.edgeFinset.card + 3 * C.card <= 3 * Fintype.card V := by
    have hsumineq := Finset.sum_le_sum (fun s hs => hslack s hs)
    have hsumconst : (∑ s ∈ C, (3 : ℕ)) = 3 * C.card := by
      rw [Finset.sum_const_nat (m := 3) (by intro s hs; rfl)]
      exact Nat.mul_comm _ _
    have hsumscaled : (∑ s ∈ C, 3 * s.card) = 3 * Fintype.card V := by
      calc
        (∑ s ∈ C, 3 * s.card) = 3 * (∑ s ∈ C, s.card) := by rw [← Finset.mul_sum]
        _ = 3 * Fintype.card V := by rw [hsum]
    calc
      N.edgeFinset.card + 3 * C.card =
          (∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card) +
            (∑ s ∈ C, (3 : ℕ)) := by rw [hedges, hsumconst]
      _ = ∑ s ∈ C, ((N.induce (s : Set V)).edgeFinset.card + 3) := by
        rw [← Finset.sum_add_distrib]
      _ <= ∑ s ∈ C, 3 * s.card := hsumineq
      _ = 3 * Fintype.card V := hsumscaled
  have hCpos : 0 < C.card := by
    by_contra h
    have hz : C.card = 0 := Nat.eq_zero_of_not_pos h
    have hC : C = ∅ := Finset.card_eq_zero.mp hz
    rw [hC, Finset.sum_empty] at hsum
    omega
  by_cases hone : C.card = 1
  · obtain ⟨s, hsC⟩ := Finset.card_eq_one.mp hone
    have hs : s ∈ C := by rw [hsC]; simp
    have hsize : s.card = Fintype.card V := by simpa [hsC] using hsum
    have hlocal' := hlocal s (by omega) (hconnected s hs)
    have hedges' : N.edgeFinset.card = (N.induce (s : Set V)).edgeFinset.card := by
      simpa [hsC] using hedges
    rw [hedges']
    simpa [hsize] using hlocal'
  · have hmany : 2 <= C.card := by omega
    have hparts : 6 <= 3 * C.card := by omega
    have hedge6 : N.edgeFinset.card + 6 <= 3 * Fintype.card V := by
      calc
        N.edgeFinset.card + 6 <= N.edgeFinset.card + 3 * C.card :=
          Nat.add_le_add_left hparts _
        _ <= 3 * Fintype.card V := htotal
    have hbound : 6 <= 3 * Fintype.card V := by omega
    exact (Nat.le_sub_iff_add_le hbound).2 hedge6
