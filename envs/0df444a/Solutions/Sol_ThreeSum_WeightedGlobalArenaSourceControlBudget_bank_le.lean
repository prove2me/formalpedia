-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceControlBudget.bank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:15:26.920316+00:00
-- url     : https://prove2.me/submissions/f2b9bc22-4791-4c9a-8afe-e4ba57d2cfcf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControls
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_strictly_sorted
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_codes_lt
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_WeightedAddresses_mem_codes_lt
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_strictly_sorted
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_codes_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceControlBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceControls
open WeightedGlobalArenaPairMass WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalCoverGoodMaps StageBounds
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaSourceControlBudget
theorem _root_.solution (m r : ℕ) : nb m r≤4^(N m r) := by
  classical
  have hn : (bankCodes m r).Nodup := (WeightedAddresses.codes_strictly_sorted _ _).nodup
  calc
    _=((bankCodes m r).toFinset).card := (List.toFinset_card_of_nodup hn).symm
    _≤(Finset.range (4^(N m r))).card := by
      apply Finset.card_le_card
      intro a ha
      exact Finset.mem_range.mpr (WeightedAddresses.mem_codes_lt (List.mem_toFinset.mp ha))
    _=_ := Finset.card_range _
end ThreeSum.WeightedGlobalArenaSourceControlBudget
