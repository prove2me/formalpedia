-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.Jm_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:33:53.737616+00:00
-- url     : https://prove2.me/submissions/e9c48fac-4dce-4bea-aa6f-d82bda091c56

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_measurableSet_dShell
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_mul


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
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (g₁ : GL (Fin n) k) (m : ℤ) :
    Jm n (fun x => φ (x * g₁.val)) m = Jm n φ (m + ord k (gdet g₁)) := by
  rw [Jm, Jm, ← integral_indicator (measurableSet_dShell _ _), ← integral_indicator (measurableSet_dShell _ _),
    ← integral_mul_right_eq_self ((dShell n (m + ord k (gdet g₁))).indicator fun g => φ g.val) g₁]
  congr 1
  funext g
  have h : g * g₁ ∈ dShell n (m + ord k (gdet g₁)) ↔ g ∈ dShell n m := by
    show ord k (gdet (g * g₁)) = _ ↔ ord k (gdet g) = m
    rw [gdet_mul, ord_mul]; omega
  by_cases hg : g ∈ dShell n m
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (h.2 hg), Units.val_mul]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt h.1 hg)]
end PositivityTheory.ThK.SplitLoc.Unr
