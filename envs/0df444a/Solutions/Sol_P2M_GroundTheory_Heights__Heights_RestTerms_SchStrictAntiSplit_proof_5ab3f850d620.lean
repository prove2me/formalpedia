-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_proof_5ab3f850d620
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:02.041303+00:00
-- url     : https://prove2.me/submissions/e84dd465-b1d2-4475-803c-71ed2baa74d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchStrictAntiSplit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_add_gap_le_b581b9fe30b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_sum_staircase_97112d8ec57a
import Theorems.Thm_UpperTheory_Reformulated_B_Yoa4_add_gap_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchStrictAntiSplit
theorem _root_.solution : SchStrictAntiSplit.Statement := by
  intro r n d hd hsum
  have hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i := by
    intro i
    have hr : 0 < r := Fin.pos i
    have h := SchStrictAntiSplit.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩
      (by simp; omega)
    omega
  refine ⟨hlow, ?_⟩
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, ?_⟩
  · have hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) =
        ∑ i : Fin r, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)
    rw [SchStrictAntiSplit.sum_staircase] at hadd
    omega
  · intro i j hij
    have h := SchStrictAntiSplit.add_gap_le hd ((j : ℕ) - i) i j (by omega)
    have := hlow i
    have := hlow j
    have : (i : ℕ) ≤ j := hij
    have : (j : ℕ) < r := j.isLt
    show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))
    omega
end SchStrictAntiSplit
end GroundTheory.Heights₂.Heights.RestTerms
