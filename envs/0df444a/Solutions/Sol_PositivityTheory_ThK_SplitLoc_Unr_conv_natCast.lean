-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.conv_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:45.176234+00:00
-- url     : https://prove2.me/submissions/21a0e483-9cf5-40fc-9ba9-adf441369fde

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
open PowerSeries
namespace PositivityTheory.ThK.SplitLoc.Unr
theorem _root_.solution {P : Polynomial ℂ} {n : ℕ} (hP : P.natDegree ≤ n) {f : ℤ → ℂ} (hf : ∀ m < 0, f m = 0) (t : ℕ) :
    conv P n f t = coeff t ((P : PowerSeries ℂ) * mk fun s => f s) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe, coeff_mk]
  unfold conv
  have h1 : ∑ j ∈ Finset.range (n + 1), P.coeff j * f ((t : ℤ) - j) =
      ∑ j ∈ Finset.range (n + t + 1), P.coeff j * f ((t : ℤ) - j) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    rw [Finset.mem_range] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have h2 : ∑ j ∈ Finset.range (t + 1), P.coeff j * f ((t : ℤ) - j) =
      ∑ j ∈ Finset.range (n + t + 1), P.coeff j * f ((t : ℤ) - j) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
    rw [Finset.mem_range] at hj
    rw [hf _ (by omega), mul_zero]
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [Nat.cast_sub (by omega)]
end PositivityTheory.ThK.SplitLoc.Unr
