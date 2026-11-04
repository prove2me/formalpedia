-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryTimeMonotone.selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:17:17.121719+00:00
-- url     : https://prove2.me/submissions/cd84ef32-63a9-4fde-9f56-e1339a28f26b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTime
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryTimeMonotone
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryTimeMonotone_counts
import Theorems.Thm_ThreeSum_LightOriginalSurvivors_length_le
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_length_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryTimeMonotone
open WeightedGlobalArenaSourceSetup WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalArenaQueryTimeMonotone
theorem _root_.solution {J : ℕ} (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    let I' := WeightedGlobalArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC
    WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I')≤
      WeightedGlobalArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I) := by
  apply counts
  · exact LightOriginalSurvivors.length_le keysB I.nB
  · exact LightOriginalSurvivors.length_le keysC I.nC
  · exact le_rfl
end ThreeSum.WeightedGlobalArenaQueryTimeMonotone
