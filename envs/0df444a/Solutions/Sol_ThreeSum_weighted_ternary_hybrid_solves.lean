-- Prove2me | solution 1 for ThreeSum.weighted_ternary_hybrid_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:36:54.694856+00:00
-- url     : https://prove2.me/submissions/64906edc-913c-41ac-8fd4-92210907f076

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryProfileFastExecution
import Definitions.Def_Submission_Weighted_Global_TernaryFinalSolver
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_solves
import Theorems.Thm_ThreeSum_WeightedGlobalConcreteProfile_Profile_fastExecution


set_option autoImplicit false
noncomputable section
open ThreeSum
open Light WeightedGlobalConcreteProfile
namespace ThreeSum
theorem _root_.solution {κ : ℕ} (P : Profile κ) :
    Solves s3Task P.hybridProgram P.hybridMain P.hybridTime P.hybridNeed :=
  TernarySolverEndBridge.hybrid_solves P.fastExecution
end ThreeSum
