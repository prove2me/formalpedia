-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.invL_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:47.331229+00:00
-- url     : https://prove2.me/submissions/cdfa8bac-bddb-4bef-8e55-a6c1d43aa8d5

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_resCard_cast_ne_zero

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
omit [MeasurableSpace k] [BorelSpace k]
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution (n d : ℕ) (ϖ : kˣ) (ν : kˣ →* ℂˣ) :
    invL n d ϖ ν = ∏ i : Fin n,
      (1 - Polynomial.C (cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) * Polynomial.X) := by
  rw [Fin.prod_univ_eq_prod_range
    (fun i => (1 - Polynomial.C (cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - i)) * Polynomial.X)) n,
    Finset.prod_range_reflect (fun i => (1 - Polynomial.C (cst d ϖ ν * (resCard k : ℂ) ^ i) * Polynomial.X)) n, invL]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sub_eq_add_neg (i : ℂ), Complex.cpow_add _ _ resCard_cast_ne_zero, Complex.cpow_natCast, cst, neg_div]
  congr 3
  ring
end PositivityTheory.ThK.SplitLoc.Unr
