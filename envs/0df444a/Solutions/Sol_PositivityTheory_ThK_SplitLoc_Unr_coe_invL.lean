-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.coe_invL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:27.747583+00:00
-- url     : https://prove2.me/submissions/b881939f-488f-4a67-a028-3929e698c33e

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_invL_eq_prod

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
    (invL n d ϖ ν : PowerSeries ℂ) = ∏ i : Fin n,
      (1 - PowerSeries.C (cst d ϖ ν * (resCard k : ℂ) ^ (n - 1 - (i : ℕ))) * PowerSeries.X) := by
  rw [invL_eq_prod, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X]
end PositivityTheory.ThK.SplitLoc.Unr
