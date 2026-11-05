-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.weighted_ternary_hybrid_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:50:15.32098+00:00
-- url     : https://prove2.me/submissions/78e0e6e1-5f73-443c-a8ed-d7bd9bd10c44

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryProfileFastExecution
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFinalSolver
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_solves
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalConcreteProfile_Profile_fastExecution


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum
open Light WeightedGlobalConcreteProfile
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum
theorem _root_.solution {κ : ℕ} (P : Profile κ) :
    Solves s3Task P.hybridProgram P.hybridMain P.hybridTime P.hybridNeed :=
  TernarySolverEndBridge.hybrid_solves P.fastExecution
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum
