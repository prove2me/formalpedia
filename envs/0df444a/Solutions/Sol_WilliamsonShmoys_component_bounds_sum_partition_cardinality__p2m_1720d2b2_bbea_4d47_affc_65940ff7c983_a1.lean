-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_partition_cardinality__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:28:06.129973+00:00
-- url     : https://prove2.me/submissions/acc1a795-9e63-4428-904f-d9663ce3789d

-- ID: a731231d-505e-4034-89ec-a538bd9426d0 | NAME: WilliamsonShmoys.component_bounds_sum_partition_cardinality__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1 | 未本地编译验证
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hnonempty : ∀ s ∈ C, s.Nonempty) :
    (∑ s ∈ C, s.card) = Fintype.card V := by
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
  have hcardU : (C.biUnion (fun s : Finset V => s)).card = ∑ s ∈ C, s.card :=
    Finset.card_biUnion hpair
  rw [hU] at hcardU
  simpa using hcardU.symm
