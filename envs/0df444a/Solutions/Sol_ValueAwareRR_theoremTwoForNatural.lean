-- Prove2me | solution 1 for ValueAwareRR.theoremTwoForNatural
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:19:07.296799+00:00
-- url     : https://prove2.me/submissions/5ed71d73-7635-4f63-9101-563def424d98

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_trueOptimal_loss
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedExactLoss_scaling
import Theorems.Thm_ValueAwareRR_normalizedResidualMax_eq_one
import Theorems.Thm_ValueAwareRR_normalizedExactLoss_minimizer_iff
import Theorems.Thm_ValueAwareRR_normalizedMaxPrefixScore_minimizer_iff
import Theorems.Thm_ValueAwareRR_normalizedDiagonalScore_minimizer_iff
import Theorems.Thm_ValueAwareRR_normalizedTrueOptimal_global_minimum
import Theorems.Thm_ValueAwareRR_normalizedProxy_maxPrefix_global_minimum
import Theorems.Thm_ValueAwareRR_normalizedProxy_diagonal_global_minimum
import Theorems.Thm_ValueAwareRR_normalizedLossRatio_exact
import Theorems.Thm_ValueAwareRR_normalizedLossRatio_lower_bound

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℕ) (hm : 2 ≤ m) : NaturalFamilyCertificate m := by
  have hmQ : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  refine ⟨normalizedResidualMax_eq_one (m : ℚ) hmQ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normalizedExactLoss_scaling, trueOptimal_loss]
    have hs : 0 < normalizationScale (m : ℚ) ^ 2 :=
      sq_pos_of_pos (normalizationScale_pos (m : ℚ) hmQ)
    nlinarith
  · exact normalizedTrueOptimal_global_minimum (m : ℚ) hmQ
  · exact normalizedExactLoss_minimizer_iff (m : ℚ) hmQ
  · exact normalizedProxy_maxPrefix_global_minimum (m : ℚ) hmQ
  · exact normalizedMaxPrefixScore_minimizer_iff (m : ℚ) hmQ
  · exact normalizedProxy_diagonal_global_minimum (m : ℚ) hmQ
  · exact normalizedDiagonalScore_minimizer_iff (m : ℚ) hmQ
  · exact normalizedLossRatio_exact (m : ℚ) hmQ
  · exact normalizedLossRatio_lower_bound (m : ℚ) hmQ
end ValueAwareRR
