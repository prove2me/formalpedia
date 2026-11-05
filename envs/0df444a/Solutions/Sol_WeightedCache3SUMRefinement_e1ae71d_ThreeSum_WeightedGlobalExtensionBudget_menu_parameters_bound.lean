-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExtensionBudget.menu_parameters_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:52:49.328527+00:00
-- url     : https://prove2.me/submissions/50fc3295-2d71-4268-8b1c-fd78159066d4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedPreparationBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalExtensionBudget_degree_le_field_size
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menu_field_upper


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExtensionBudget
open ThreeSum.TernaryExtensionEncoding
open Filter Real WeightedGlobalSignedPadding WeightedGlobalCoverScale
open WeightedGlobalSignedPreparationBudget
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExtensionBudget
theorem _root_.solution (J K : ℕ) :
    p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1≤
      (48*p^(4*K+1)+3)*(J+1) := by
  have hq := menu_field_upper (p := p) (J+2) K
  have hd := degree_le_field_size (p := p) (menuDegree p (J+2) K)
  have hmul : 8*p^(4*K+1)*(J+2+1)≤24*p^(4*K+1)*(J+1) := by
    have hh := Nat.mul_le_mul_left (8*p^(4*K+1)) (show J+2+1≤3*(J+1) by omega)
    nlinarith
  nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExtensionBudget
