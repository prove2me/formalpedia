-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalDigitSpan.physical_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:07.359645+00:00
-- url     : https://prove2.me/submissions/39ff93e2-e627-4c00-8132-93f35cd3981b

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_reversal_span

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}
namespace ThreeSum.TernaryPhysicalDigitSpan
theorem _root_.solution (rows : List (Fin J → K)) (row : Fin (J+2) → K) :
    physicalDigits row∈oldSpan (rows.map (reversal J)) ↔ row∈forbidden rows :=
  reversal_span rows (digitProjection J row)
end ThreeSum.TernaryPhysicalDigitSpan
