-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_antisymmetrize_blockVandermonde_e253c2e15948
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:32.744402+00:00
-- url     : https://prove2.me/submissions/4a6619c1-ca1a-4f80-94c0-4d02435c1961

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_blockPerm_c7329941447d

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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) :
    antisymmetrize f N (blockVandermonde f N) =
      ((N.factorial : ℚ) ^ f) • blockVandermonde f N := by
  simp only [antisymmetrize, blockPermute_blockVandermonde, smul_smul, blockSign_mul_self, one_smul,
    Finset.sum_const, Finset.card_univ, card_blockPerm]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  push_cast
  rfl
end GroundTheory.Heights₂.Heights.RestTerms.Flag
