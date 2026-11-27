-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:17:03.965779+00:00
-- url     : https://prove2.me/submissions/e67619c3-ec0e-40ba-b403-b7e15fbbd09b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RegularLocalRegularSequence_ExistsIsRegularOfListEqMaximalIdeal
import Theorems.Thm_PI_UnitaryGroupMassFormula_RLRS_IsRegularLocalRing_exists_list_of_spanFinrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.RLRS
open PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
open IsLocalRing RingTheory.Sequence
open scoped Pointwise
universe u
namespace PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
theorem _root_.solution (A : Type u) [CommRing A]
    [IsRegularLocalRing A] :
    ∃ xs : List A, Ideal.ofList xs = maximalIdeal A ∧
      (xs.length : WithBot ℕ∞) = ringKrullDim A ∧ IsRegular A xs := by
  obtain ⟨xs, h1, h2, h3⟩ := exists_list_of_spanFinrank_eq _ A rfl
  refine ⟨xs, h1, ?_, ?_⟩
  · rw [h2]
    exact _root_.IsRegularLocalRing.spanFinrank_maximalIdeal
  · refine RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A ?_ h3
    intro r hr
    rw [← h1]
    exact Ideal.subset_span hr
end PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
