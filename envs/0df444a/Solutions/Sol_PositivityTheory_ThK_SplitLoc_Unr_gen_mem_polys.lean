-- Prove2me | solution 1 for PositivityTheory.ThK.SplitLoc.Unr.gen_mem_polys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:35.448148+00:00
-- url     : https://prove2.me/submissions/4d1be23a-ffae-418c-ad9d-0aeb00f6b6cf

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_coeff_prod_mk
import Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_linear_mul_piece_mem_polys
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
theorem _root_.solution {n : ℕ} (γ : Fin n → ℂ) (M : ℕ) (T : (Fin n → ℕ) → ℂ)
    (hT : ∀ a, T a = (∏ i, γ i ^ (a i - M)) * T (fun i => min (a i) M)) :
    (∏ i, (1 - C (γ i) * X)) * mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, T a) ∈ polys := by
  classical
  have key : (mk (fun t => ∑ a ∈ Finset.piAntidiag Finset.univ t, T a) : PowerSeries ℂ) =
      ∑ b ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (M + 1)),
        C (T b) * ∏ i, mk (fun t => if min t M = b i then γ i ^ (t - M) else 0) := by
    ext t
    rw [coeff_mk, map_sum]
    simp only [coeff_C_mul, coeff_prod_mk, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (fun i => min (a i) M)]
    · rw [hT a, mul_comm]
      simp
    · intro b _ hb
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (Ne.symm hi)), mul_zero]
    · intro h
      exact absurd (Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (by omega)) h
  rw [key, Finset.mul_sum]
  refine Subring.sum_mem _ fun b _ => ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  refine Subring.mul_mem _ ⟨Polynomial.C (T b), by simp⟩ ?_
  exact Subring.prod_mem _ fun i _ => linear_mul_piece_mem_polys _ _ _
end PositivityTheory.ThK.SplitLoc.Unr
