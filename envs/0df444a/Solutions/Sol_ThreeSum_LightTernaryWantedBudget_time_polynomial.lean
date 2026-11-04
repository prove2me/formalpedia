-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedBudget.time_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:16.231886+00:00
-- url     : https://prove2.me/submissions/d4b8c7cb-352e-41f4-aae8-960a22863786

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Theorems.Thm_ThreeSum_LightTernaryWantedBudget_node_budget
import Theorems.Thm_ThreeSum_LightBalancedOffset_time_bound
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeyRow_time_bound
import Theorems.Thm_ThreeSum_LightLocalKeys_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_957e2f25efb6cbcf
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedBudget
open LightTernaryWantedCanonical
namespace ThreeSum.LightTernaryWantedBudget
theorem _root_.solution (P C V A J : ℕ) (hC : 1 ≤ C)
    (hV : V ≤ A*(P+1)^J) :
    time P C V J ≤ 1000*(A+2*P+4)*(J+1)^2*C^J := by
  have hA : A ≤ 2^A := (Nat.lt_two_pow_self).le
  have hP : P+1 ≤ 2^(P+1) := (Nat.lt_two_pow_self).le
  have hp : (P+1)^J ≤ (2^(P+1))^J := Nat.pow_le_pow_left hP J
  have hv : V ≤ 2^(A+(P+1)*J) := by
    calc
      V ≤ A*(P+1)^J := hV
      _ ≤ 2^A*(2^(P+1))^J := Nat.mul_le_mul hA hp
      _ = _ := by rw [← pow_mul,← pow_add]
  have hn := node_budget P V (A+(P+1)*J) hv
  have hl : P+(A+(P+1)*J)+3 ≤ (A+2*P+4)*(J+1) := by nlinarith
  have hlin : overhead P V+stepCost V+40 ≤ 1000*(A+2*P+4)*(J+1) := by
    calc
      _ ≤ 1000*(P+(A+(P+1)*J)+3) := hn
      _ ≤ 1000*((A+2*P+4)*(J+1)) := Nat.mul_le_mul_left _ hl
      _ = _ := by ring
  calc
    time P C V J ≤ (overhead P V+stepCost V+40)*(J+1)*C^J := time_bound P C V hC J
    _ ≤ (1000*(A+2*P+4)*(J+1))*(J+1)*C^J :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlin)
    _ = _ := by ring
end ThreeSum.LightTernaryWantedBudget
