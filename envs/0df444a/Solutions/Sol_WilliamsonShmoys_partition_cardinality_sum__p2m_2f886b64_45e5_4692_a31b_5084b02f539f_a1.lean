-- Prove2me | solution 1 for WilliamsonShmoys.partition_cardinality_sum__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T20:24:34.752841+00:00
-- url     : https://prove2.me/submissions/55edd521-d7c1-40fc-8709-3e467c3ad69b

import Mathlib

set_option autoImplicit false
set_option linter.unnecessarySimpa false

theorem solution {V : Type} [Fintype V] (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) :
    (∑ C ∈ parts, Fintype.card {x : V // x ∈ C}) = Fintype.card V := by
  classical
  have hcardC (C : Finset V) : Fintype.card {x : V // x ∈ C} = C.card := by
    simpa using (Fintype.card_coe C)
  simp_rw [hcardC]
  have hU : parts.biUnion (fun C : Finset V => C) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    obtain ⟨C, hCp, hvC⟩ := hcover v
    exact Finset.mem_biUnion.mpr ⟨C, hCp, hvC⟩
  have hdisj : (parts : Set (Finset V)).PairwiseDisjoint (fun C : Finset V => C) := by
    intro C hC D hD hCD
    exact hdisjoint C hC D hD hCD
  have hcardU : (parts.biUnion (fun C : Finset V => C)).card = ∑ C ∈ parts, C.card :=
    Finset.card_biUnion hdisj
  rw [hU] at hcardU
  simpa using hcardU.symm
