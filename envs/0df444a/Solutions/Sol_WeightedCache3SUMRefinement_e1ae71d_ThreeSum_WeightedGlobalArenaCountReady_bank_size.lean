-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCountReady.bank_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T13:26:36.731815+00:00
-- url     : https://prove2.me/submissions/29f369d8-9a1c-411e-a2fc-67fa2dae49ca

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceValues
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCountReady
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_bank_card_le

namespace WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
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
end
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCountReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open WeightedGlobalBank TernaryCodeSemantics LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCountReady
theorem _root_.solution (hN : 0<N m r) : nb m r<2^(2*N m r) := by
  unfold nb bankCodes
  rw [WeightedBankEnumeration.codes_length_eq_bank_card,←four_pow]
  exact (WeightedGlobalBank.bank_card_le _ _).trans_lt (Nat.pow_lt_pow_left (by decide) (by omega))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCountReady
