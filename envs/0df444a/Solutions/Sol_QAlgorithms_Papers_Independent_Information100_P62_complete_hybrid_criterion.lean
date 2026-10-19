-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.complete_hybrid_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:57:21.863991+00:00
-- url     : https://prove2.me/submissions/b3aec45e-bca3-4e7f-bd63-f0b1b86d6ebb

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_capacity_necessity_and_maximality
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_finite_domination_criterion

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem solution [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) :
    (HasDominating F ↔ (∀ d ∈ Icc 1 (dmax F), 0 ≤ QAlgorithms.Papers.Independent.Information100.P62.multiplicity F d) ∧
      ∃ A, capacityAlgebra F = some A ∧ Transmits F A ∧ forbidden A ∩ transmission F = ∅) ∧
    (∀ A, capacityAlgebra F = some A → Transmits F A →
      forbidden A ∩ transmission F = ∅ → Dominating F A) := by
  constructor
  · constructor
    · rintro ⟨A, hA⟩
      obtain ⟨hnonneg, hcap⟩ := (capacity_necessity_and_maximality F hF).1 A hA
      have hfinite := (finite_domination_criterion F hF A hA.1.1).mp hA
      exact ⟨hnonneg, A, hcap, hfinite⟩
    · rintro ⟨_, A, _, htrans, hforbid⟩
      exact ⟨A, (finite_domination_criterion F hF A htrans.1).mpr ⟨htrans, hforbid⟩⟩
  · intro A _ htrans hforbid
    exact (finite_domination_criterion F hF A htrans.1).mpr ⟨htrans, hforbid⟩

#print axioms solution
