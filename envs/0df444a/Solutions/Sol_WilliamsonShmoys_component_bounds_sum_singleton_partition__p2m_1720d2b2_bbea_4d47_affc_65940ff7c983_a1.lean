-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_singleton_partition__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:30:20.290212+00:00
-- url     : https://prove2.me/submissions/4c497887-995a-4d27-a2c6-2d126d645218

-- ID: cead4212-c380-4992-bb07-66f494ce734c | NAME: WilliamsonShmoys.component_bounds_sum_singleton_partition__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1 | 未本地编译验证
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hconnected : ∀ s ∈ C, (N.induce (s : Set V)).Connected)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hlocal : ∀ s : Finset V, 3 <= s.card ->
      (N.induce (s : Set V)).Connected ->
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6)
    (hsingle : C.card = 1) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  have hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t := by
    intro s hs t ht hst
    rw [Finset.disjoint_left]
    intro v hvs hvt
    obtain ⟨u, hu, huniq⟩ := hpartition v
    have hsu : s = u := huniq s ⟨hs, hvs⟩
    have htu : t = u := huniq t ⟨ht, hvt⟩
    exact hst (hsu.trans htu.symm)
  have hU : C.biUnion (fun s : Finset V => s) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    obtain ⟨s, hs, _⟩ := hpartition v
    exact Finset.mem_biUnion.mpr ⟨s, hs.1, hs.2⟩
  have hpair : (C : Set (Finset V)).PairwiseDisjoint (fun s : Finset V => s) := by
    intro s hs t ht hst
    exact hdisj s hs t ht hst
  have hsum : (∑ s ∈ C, s.card) = Fintype.card V := by
    have hcardU : (C.biUnion (fun s : Finset V => s)).card = ∑ s ∈ C, s.card :=
      Finset.card_biUnion hpair
    rw [hU] at hcardU
    simpa using hcardU.symm
  obtain ⟨s0, hsC⟩ := Finset.card_eq_one.mp hsingle
  have hs0_mem : s0 ∈ C := by simp [hsC]
  have hs0_card : s0.card = Fintype.card V := by
    rw [hsC] at hsum
    simpa using hsum
  have h3 : 3 <= s0.card := by
    rw [hs0_card]
    exact hcard
  have hloc := hlocal s0 h3 (hconnected s0 hs0_mem)
  calc
    N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card := hedges
    _ = (N.induce (s0 : Set V)).edgeFinset.card := by rw [hsC]; simp
    _ <= 3 * s0.card - 6 := hloc
    _ = 3 * Fintype.card V - 6 := by rw [hs0_card]
