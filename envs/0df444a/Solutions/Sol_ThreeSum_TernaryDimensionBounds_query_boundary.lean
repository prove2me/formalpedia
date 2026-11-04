-- Prove2me | solution 1 for ThreeSum.TernaryDimensionBounds.query_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:49.211999+00:00
-- url     : https://prove2.me/submissions/dd0c2234-fec2-4569-a882-76743b90d837

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_output_rank

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters
namespace ThreeSum.TernaryDimensionBounds
theorem _root_.solution {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : rank Q+1-bankCut m j=queryDeficit m j := by
  rw [output_rank hQ]
  unfold bankCut queryDeficit
  ring_nf
  omega
end ThreeSum.TernaryDimensionBounds
