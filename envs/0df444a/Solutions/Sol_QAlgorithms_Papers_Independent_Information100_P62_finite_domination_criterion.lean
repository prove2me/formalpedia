-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.finite_domination_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:40:35.867906+00:00
-- url     : https://prove2.me/submissions/9d5270ee-bb44-40ec-9167-ed9e87a28f30

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_finite_obstructions
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_transmission_lower

noncomputable section
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P62

/-- Theorem 4.11 of Salzmann–Singh, arXiv:2609.40054v1, PDF page 37.
A lower transmission set is dominated by A precisely when it contains A and
contains no minimal obstruction to embedding into A. -/
theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Dominating F A ↔ Transmits F A ∧ forbidden A ∩ transmission F = ∅ := by
  classical
  constructor
  · rintro ⟨htrans, hdom⟩
    refine ⟨htrans, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro B hB
    exact hB.1.2.1 (hdom B hB.2)
  · rintro ⟨htrans, hempty⟩
    refine ⟨htrans, ?_⟩
    intro C hC
    by_contra hnot
    obtain ⟨B, hB, hBC⟩ := (finite_obstructions A hA).2.2 C hC.1 |>.mp hnot
    have htransB : Transmits F B := transmission_lower F hF B C hB.1 hC hBC
    have hmem : B ∈ forbidden A ∩ transmission F := ⟨hB, htransB⟩
    exact Set.notMem_empty B (hempty ▸ hmem)

#print axioms solution
