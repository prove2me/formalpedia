-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan.done_keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:59:33.217736+00:00
-- url     : https://prove2.me/submissions/054b4b33-1234-4fe7-bc6e-89c4a0dea13f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaScoreScan
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_cell_protected_ne
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaScoreScan_store_other
import Theorems.Thm_Light_Ends_store


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
open LightWeightedGlobalControllerFactory LightWeightedGlobalSeedScoreFactory
open WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
set_option maxHeartbeats 2000000
variable {p r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
theorem _root_.solution {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K i : ℕ} {ν ξ : ℕ→ℤ} (hi : i < I.capacity)
    (done : (D.candidate i).Done K ν ξ) : KeepInputs I ν ξ := by
  obtain ⟨ζ,hkeep,rfl⟩ := done
  change KeepInputs I ν (store I i (values D K i) ζ)
  intro x hx
  rw [store_other (fun c hc => cell_protected_ne hc hi hx)]
  exact hkeep x hx.2.1 hx.2.2
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaScoreScan
