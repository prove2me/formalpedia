-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.ord_of_mem_shellSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:15.701546+00:00
-- url     : https://prove2.me/submissions/b9a40efe-0909-40a7-8103-ec5357f753be

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_prod_eq
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_ord_zpow_eq
import Theorems.Thm_GlobalTheory_SmGL_ord_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_det_diagGL
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_mul
import Theorems.Thm_GlobalTheory_SplitFlip_mem_shellSet
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO


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
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {n : ℕ} {e : Fin n → ℤ} {g : GL (Fin n) k}
    (hg : g ∈ shellSet ϖ e) : ord k (gdet g) = ∑ i, e i := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
  rw [gdet_mul, gdet_mul, ord_mul, ord_mul, ord_eq_zero (valuation_gdet_of_mem_KO hx),
    ord_eq_zero (valuation_gdet_of_mem_KO hy), zero_add, add_zero, gdet, det_diagGL, ord_prod_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [ord_zpow_eq, ord_eq_one hϖ, mul_one]
end PositivityTheory.ThK.SplitLoc.Unr
