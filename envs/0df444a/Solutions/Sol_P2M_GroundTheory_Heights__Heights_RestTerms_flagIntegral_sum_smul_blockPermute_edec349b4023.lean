-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_sum_smul_blockPermute_edec349b4023
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:51.039801+00:00
-- url     : https://prove2.me/submissions/ae0893b7-69f8-4a1d-b8d3-6ad72c9aed88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralAntisymmetrize
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_add_970f926c8cdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_zero_b1c44130856d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Flag.flagIntegral_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Flag.flagIntegral_add, ih, smul_eq_C_mul,
      Flag.flagIntegral_C_mul]
end GroundTheory.Heights₂.Heights.RestTerms
