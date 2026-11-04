-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSeedCoefficientBudget.wanted_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:48:27.865386+00:00
-- url     : https://prove2.me/submissions/ef2b788b-4683-42f7-82e3-67da27bdbd85

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_Submission_Weighted_Global_TernarySeedCoefficientBudget
import Theorems.Thm_ThreeSum_LightTernaryWantedBudget_node_budget


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalSeedCoefficientBudget
theorem _root_.solution (p A J j : ℕ) (hj : j≤J) :
    (LightTernaryWantedCanonical.overhead p (A*(p+1)^j)+
      LightTernaryWantedCanonical.stepCost (A*(p+1)^j)+40)*(j+1)≤
      (1000*(A+2*p+4))*(J+1)^2 := by
  have hA : A≤2^A := (Nat.lt_two_pow_self).le
  have hP : p+1≤2^(p+1) := (Nat.lt_two_pow_self).le
  have hv : A*(p+1)^j≤2^(A+(p+1)*j) := by
    calc
      _≤2^A*(2^(p+1))^j := Nat.mul_le_mul hA (Nat.pow_le_pow_left hP j)
      _=_ := by rw [←pow_mul,←pow_add]
  have hn := LightTernaryWantedBudget.node_budget p (A*(p+1)^j) (A+(p+1)*j) hv
  have hlin : p+(A+(p+1)*j)+3≤(A+2*p+4)*(J+1) := by nlinarith
  have hlin' := hn.trans (Nat.mul_le_mul_left 1000 hlin)
  have hh := Nat.mul_le_mul hlin' (Nat.add_le_add_right hj 1)
  nlinarith only [hh]
end ThreeSum.WeightedGlobalSeedCoefficientBudget
