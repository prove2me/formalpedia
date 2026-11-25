-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.gen_geom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:09.763403+00:00
-- url     : https://prove2.me/submissions/2bed0e04-5139-44e9-bd4d-aac365818dcd

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_coeff_prod_geom
import Theorems.Thm_GlobalTheory_CompleteHomogeneousBound_geom_mul_linear


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
open PowerSeries
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {n : ℕ} (γ : Fin n → ℂ) :
    (∏ i, (1 - C (γ i) * X)) * mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i, γ i ^ a i) = 1 := by
  have key : (mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, ∏ i, γ i ^ a i) : PowerSeries ℂ) =
      ∏ i, mk (fun t => γ i ^ t) := by
    ext t
    rw [coeff_mk, GlobalTheory.CompleteHomogeneousBound.coeff_prod_geom]
  rw [key, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [mul_comm, GlobalTheory.CompleteHomogeneousBound.geom_mul_linear]
end PositivityTheory.ThK.SplitLoc.Unr
