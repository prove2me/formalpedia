-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagPowerSumPreimage_proof_f6c76dbd20e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:20.744711+00:00
-- url     : https://prove2.me/submissions/a1b68fb0-8412-4ecc-bb99-4ffd4eb74719

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagPowerSumPreimage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sum_Icc_one_eq_sum_fin_6fc36c803c22
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_constantCoeff_powerSumHom_cd225d5dc115
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c


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
namespace FlagPowerSumPreimage
theorem _root_.solution : FlagPowerSumPreimage.Statement := by
  intro N T hT
  choose Sf hSf using fun l => Flag.exists_powerSumHom_eq (hT l)
  refine ⟨∑ i : Fin N, X i * Sf (i.val + 1), ?_, ?_⟩
  · rw [sum_Icc_one_eq_sum_fin N (fun l => psum (Fin N) ℚ l * T l), map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, hSf]
    simp [powerSumHom]
  · intro k hk1 hkN
    set j : Fin N := ⟨k - 1, by omega⟩ with hj
    rw [coeff_sum, Finset.sum_eq_single j]
    · rw [coeff_X_mul', if_pos (by simp), tsub_self, ← constantCoeff_eq,
        ← Flag.constantCoeff_powerSumHom, hSf]
      have : j.val + 1 = k := by simp [hj]; omega
      rw [this]
    · intro i _ hij
      rw [coeff_X_mul', if_neg]
      simp only [Finsupp.mem_support_iff, ne_eq]
      rw [Finsupp.single_apply, if_neg (fun h => hij h.symm)]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h
end FlagPowerSumPreimage
end GroundTheory.Heights₂.Heights.RestTerms
