-- Prove2me | solution 1 for WilliamsonShmoys_partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:28:06.104277+00:00
-- url     : https://prove2.me/submissions/f28f7226-77bc-4804-912e-5bcaf16da43a

-- ID: 9dc6bd7e-b9f9-448b-a405-5231d2c1217c | NAME: WilliamsonShmoys_partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a5 | 未本地编译验证
import Mathlib
set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] (parts : Finset (Finset V)) (hcover : ∀ v, ∃ s ∈ parts, v ∈ s) (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) : ∑ s ∈ parts, s.card = Fintype.card V := by
  classical
  have hU : parts.biUnion (fun s : Finset V => s) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    obtain ⟨s, hs, hv⟩ := hcover v
    exact Finset.mem_biUnion.mpr ⟨s, hs, hv⟩
  have hpair : (parts : Set (Finset V)).PairwiseDisjoint (fun s : Finset V => s) := by
    intro s hs t ht hst
    exact hdisj s hs t ht hst
  have hcardU : (parts.biUnion (fun s : Finset V => s)).card = ∑ s ∈ parts, s.card :=
    Finset.card_biUnion hpair
  rw [hU] at hcardU
  simpa using hcardU.symm
