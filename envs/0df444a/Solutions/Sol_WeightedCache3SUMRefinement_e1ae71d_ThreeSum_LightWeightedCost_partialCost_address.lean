-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost.partialCost_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:18.959686+00:00
-- url     : https://prove2.me/submissions/72e8e7bf-77a0-4849-8aba-99dd15e82b6e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_digitCost_eq


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
theorem _root_.solution {N : ℕ} (w : TritWord N) : partialCost N (address w) N=WeightedBankEnumeration.cacheCost w := by
  unfold partialCost WeightedBankEnumeration.cacheCost WeightedCache.cost
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  rw [show digitAt N (address w) i.val=(w i).val from digit_eq w i]
  exact WeightedBankEnumeration.digitCost_eq (w i)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
