-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.dvd_out_sub_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:45.446897+00:00
-- url     : https://prove2.me/submissions/3bd9d081-8adb-4550-87a2-6343a6bfca0f

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_IwahoriInj_Inj_trans
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
variable [MeasurableSpace k] [BorelSpace k]
open GlobalTheory.SatakeBound
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {R : Type} [CommRing R] (p : R) (m M : ℕ) (x : R ⧸ Ideal.span {p ^ m}) :
    p ^ M ∣ x.out - (Ideal.Quotient.factor (span_pow_le_min p m M) x).out := by
  rcases le_total m M with h | h
  · have key : ∀ m' (_ : m = m') (H : Ideal.span {p ^ m} ≤ Ideal.span {p ^ m'}),
        (Ideal.Quotient.factor H x).out = x.out := fun m' e H => by
      subst e
      rw [Ideal.Quotient.factor_eq]; rfl
    rw [key _ (min_eq_left h).symm, sub_self]
    exact dvd_zero _
  · have h1 : p ^ min m M ∣ x.out - (Ideal.Quotient.factor (span_pow_le_min p m M) x).out := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out,
        ← Ideal.Quotient.factor_mk (span_pow_le_min p m M), Ideal.Quotient.mk_out]
    exact (pow_dvd_pow p (le_min h le_rfl)).trans h1
end PositivityTheory.ThK.SplitLoc.Unr
