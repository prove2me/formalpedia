-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaCountReady.bank_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:48:58.779244+00:00
-- url     : https://prove2.me/submissions/5f30c5c4-cf2b-4dcd-9b44-d23f36740f9c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCountReady
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_le
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_WeightedGlobalBank_bank_card_le

noncomputable section
namespace ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
private theorem four_pow (n : ℕ) : 4^n=2^(2*n) := by rw [Nat.pow_mul]
end ThreeSum.WeightedGlobalArenaCountReady
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaCountReady
theorem _root_.solution (hN : 0<N m r) : nb m r<2^(2*N m r) := by
  unfold nb bankCodes
  rw [WeightedBankEnumeration.codes_length_eq_bank_card,←four_pow]
  exact (WeightedGlobalBank.bank_card_le _ _).trans_lt (Nat.pow_lt_pow_left (by decide) (by omega))
end ThreeSum.WeightedGlobalArenaCountReady
