-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchPowerSumAtRootsOfUnity_proof_16d614cef0da
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:29.135845+00:00
-- url     : https://prove2.me/submissions/025ad3dc-a315-4e45-849f-88b573804c47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchPowerSumAtRootsOfUnity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchPowerSumAtRootsOfUnity_rootOfUnity_isPrimitiveRoot_1a8214c21b13

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchPowerSumAtRootsOfUnity
theorem _root_.solution : SchPowerSumAtRootsOfUnity.Statement := by
  intro N k j hk hkN hj
  have hprim := SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot hk
  simp only [psum, map_sum, map_pow, aeval_X]
  have hsum : ∑ i : Fin N, rootOfUnityPoint N k i ^ j =
      ∑ i ∈ range k, (rootOfUnity k ^ j) ^ i := by
    unfold rootOfUnityPoint
    rw [Fin.sum_univ_eq_sum_range (fun i => (if i < k then rootOfUnity k ^ i else 0) ^ j) N,
      ← Finset.sum_range_add_sum_Ico _ hkN]
    rw [Finset.sum_eq_zero (s := Ico k N) (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp [show ¬ i < k by omega, zero_pow (show j ≠ 0 by omega)]), add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hi, ← pow_mul, mul_comm]
  rw [hsum]
  split_ifs with hd
  · have h1 : rootOfUnity k ^ j = 1 := (hprim.pow_eq_one_iff_dvd j).2 hd
    simp [h1]
  · have h1 : rootOfUnity k ^ j ≠ 1 := fun h => hd ((hprim.pow_eq_one_iff_dvd j).1 h)
    have h2 : (rootOfUnity k ^ j) ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]
end SchPowerSumAtRootsOfUnity
end GroundTheory.Heights₂.Heights.RestTerms
