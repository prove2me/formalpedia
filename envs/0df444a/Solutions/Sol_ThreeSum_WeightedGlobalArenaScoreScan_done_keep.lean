-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaScoreScan.done_keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:45:17.157204+00:00
-- url     : https://prove2.me/submissions/094b17de-121c-4627-9b49-0ba732f0a8f7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_cell_protected_ne
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_store_other
import Theorems.Thm_Light_Ends_store


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K i : ℕ} {ν ξ : ℕ→ℤ} (hi : i < I.capacity)
    (done : (D.candidate i).Done K ν ξ) : KeepInputs I ν ξ := by
  obtain ⟨ζ,hkeep,rfl⟩ := done
  change KeepInputs I ν (store I i (values D K i) ζ)
  intro x hx
  rw [store_other (fun c hc => cell_protected_ne hc hi hx)]
  exact hkeep x hx.2.1 hx.2.2
end ThreeSum.WeightedGlobalArenaScoreScan
