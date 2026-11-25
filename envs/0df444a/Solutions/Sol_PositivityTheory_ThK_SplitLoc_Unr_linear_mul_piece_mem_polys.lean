-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.linear_mul_piece_mem_polys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:36.816805+00:00
-- url     : https://prove2.me/submissions/122f130f-749f-4d3e-a9ba-df482d249be4

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_mem_polys_of_coeff

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
theorem _root_.solution (γ : ℂ) (M b : ℕ) :
    (1 - C γ * X) * mk (fun t => if min t M = b then γ ^ (t - M) else 0) ∈ polys := by
  refine mem_polys_of_coeff (M + 1) fun t ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have h1 : min (s + 1) M = M := by omega
  have h2 : min s M = M := by omega
  have h3 : s + 1 - M = s - M + 1 := by omega
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_mk, h1, h2, h3]
  split_ifs
  · ring
  · ring
end PositivityTheory.ThK.SplitLoc.Unr
