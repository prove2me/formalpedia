-- Prove2me | solution 1 for WilliamsonShmoys.partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:28:06.146196+00:00
-- url     : https://prove2.me/submissions/44ebe98b-ed66-4406-9572-3db8634c0a1f

-- ID: f9e492cb-48f2-4892-9337-38d2f2723693 | NAME: WilliamsonShmoys.partition_card_sum__p2m_fd88c45a_7ea7_48a7_9749_c5d6b2241812_a1 | 未本地编译验证
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] (parts : Finset (Finset V)) (hcover : ∀ v, ∃ s ∈ parts, v ∈ s) (hdisj : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) : (∑ s ∈ parts, s.card) = Fintype.card V := by
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
