-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_not_mem_zeroLocus_multiIrrelevantIdeal_4f8d0c60fed7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:02.698666+00:00
-- url     : https://prove2.me/submissions/d6df094a-b4a3-43ac-a9b4-221aa29682c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (z : (Σ k, ι k) → ℂ) :
    z ∉ zeroLocus ℂ (multiIrrelevantIdeal ι) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  rw [multiIrrelevantIdeal, zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, not_forall, map_prod, aeval_X]
  constructor
  · rintro ⟨i, hi⟩ k
    exact ⟨i k, fun h => hi (Finset.prod_eq_zero (Finset.mem_univ k) h)⟩
  · intro h
    choose i hi using h
    exact ⟨i, Finset.prod_ne_zero_iff.mpr fun k _ => hi k⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
