-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSourceCertificate.source_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:17:44.479961+00:00
-- url     : https://prove2.me/submissions/7eea9feb-9670-4368-b6dd-3c48f4499bf3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCertificate_source_typed
import Theorems.Thm_ThreeSum_TernaryConvolution_factorial_eq_power_two


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceCertificate
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup TernaryCanonicalDictionaries WeightedGlobalNativeCompleteFrontend
open LightTernarySourceHost TernaryCodeSemantics
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaSourceCertificate
theorem _root_.solution (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (j : ℕ) (hj : j<LightTernarySourceHost.size (source (r := r) maps cap I right).xs r) :
    ((source (r := r) maps cap I right).factor : ℤ)=
      TernaryConvolution.factorial ((WeightedBankCanonical.enumeration (N m r) (cut m r)).word
        ((source (r := r) maps cap I right).key j)) := by
  rw [TernaryConvolution.factorial_eq_power_two,source_typed maps cap I right j hj 2]
  rfl
end ThreeSum.WeightedGlobalArenaSourceCertificate
