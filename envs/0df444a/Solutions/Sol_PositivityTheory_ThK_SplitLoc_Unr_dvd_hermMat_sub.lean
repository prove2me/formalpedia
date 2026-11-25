-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.dvd_hermMat_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:18.751577+00:00
-- url     : https://prove2.me/submissions/b3f0ac95-c66b-40be-8e6b-417fe306fd92

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_dvd_out_sub_out
import Theorems.Thm_GlobalTheory_SatakeBound_hermMat_lt


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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (p : R) (a : Fin n → ℕ) (M : ℕ) (c : HermIdx p a)
    (i j : Fin n) : p ^ M ∣ hermMat p a c i j - hermMat p _ (hermRed p a M c) i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hermMat_lt _ h, hermMat_lt _ h]
    exact dvd_out_sub_out p (a i) M _
  · rw [hermMat_diag, hermMat_diag]
    rcases le_total (a i) M with h | h
    · rw [min_eq_left h, sub_self]; exact dvd_zero _
    · rw [min_eq_right h]; exact dvd_sub (pow_dvd_pow p h) dvd_rfl
  · rw [hermMat_gt _ h, hermMat_gt _ h, sub_self]; exact dvd_zero _
end PositivityTheory.ThK.SplitLoc.Unr
