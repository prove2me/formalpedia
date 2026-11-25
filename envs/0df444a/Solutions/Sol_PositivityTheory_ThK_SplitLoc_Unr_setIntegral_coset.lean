-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.setIntegral_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:59.949808+00:00
-- url     : https://prove2.me/submissions/96d2c402-c1e6-4d36-9679-ceb9dccf48ba

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



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
theorem _root_.solution {n : ℕ} (φ : Matrix (Fin n) (Fin n) k → ℂ) (h : GL (Fin n) k) :
    ∫ g in {g | h⁻¹ * g ∈ KO k (Fin n)}, φ g.val ∂haarVol (KO k (Fin n)) = cosetInt φ h.val := by
  have ho : IsOpen {g | h⁻¹ * g ∈ KO k (Fin n)} := isOpen_KO.preimage (continuous_const_mul h⁻¹)
  rw [cosetInt, ← integral_indicator ho.measurableSet, ← integral_indicator isOpen_KO.measurableSet,
    ← integral_mul_left_eq_self _ h]
  congr 1
  funext g
  by_cases hg : g ∈ KO k (Fin n)
  · rw [Set.indicator_of_mem (by simpa using hg), Set.indicator_of_mem hg, Units.val_mul]
  · rw [Set.indicator_of_notMem (by simpa using hg), Set.indicator_of_notMem hg]
end PositivityTheory.ThK.SplitLoc.Unr
