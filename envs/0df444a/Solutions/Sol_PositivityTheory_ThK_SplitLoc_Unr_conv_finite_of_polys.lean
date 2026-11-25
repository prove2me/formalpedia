-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.conv_finite_of_polys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:22.038907+00:00
-- url     : https://prove2.me/submissions/89e15177-6847-46c8-bad2-396e8f11852d

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_natCast
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_conv_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} (hf : ∀ m < 0, f m = 0)
    (h : (P : PowerSeries ℂ) * PowerSeries.mk (fun s : ℕ => f s) ∈ polys) : (Function.support (conv P n f)).Finite := by
  obtain ⟨Q, hQ⟩ := h
  refine (Set.finite_Icc (0 : ℤ) Q.natDegree).subset fun m hm => ?_
  by_contra hc
  apply hm
  rcases lt_or_ge m 0 with h0 | h0
  · exact conv_neg hf h0
  · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [conv_natCast hP hf, ← hQ, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    by_contra hl
    exact hc ⟨h0, by exact_mod_cast not_lt.1 hl⟩
end PositivityTheory.ThK.SplitLoc.Unr
