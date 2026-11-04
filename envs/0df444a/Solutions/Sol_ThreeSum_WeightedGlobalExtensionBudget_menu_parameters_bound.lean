-- Prove2me | solution 1 for ThreeSum.WeightedGlobalExtensionBudget.menu_parameters_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:45:43.898561+00:00
-- url     : https://prove2.me/submissions/20a95d68-f731-43e0-8bd7-477c121c74b4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Theorems.Thm_ThreeSum_WeightedGlobalExtensionBudget_degree_le_field_size
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menu_field_upper


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExtensionBudget
open ThreeSum.TernaryExtensionEncoding
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalSignedPreparationBudget
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalExtensionBudget
theorem _root_.solution (J K : ℕ) :
    p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1≤
      (48*p^(4*K+1)+3)*(J+1) := by
  have hq := menu_field_upper (p := p) (J+2) K
  have hd := degree_le_field_size (p := p) (menuDegree p (J+2) K)
  have hmul : 8*p^(4*K+1)*(J+2+1)≤24*p^(4*K+1)*(J+1) := by
    have hh := Nat.mul_le_mul_left (8*p^(4*K+1)) (show J+2+1≤3*(J+1) by omega)
    nlinarith
  nlinarith
end ThreeSum.WeightedGlobalExtensionBudget
