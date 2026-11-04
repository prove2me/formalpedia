-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalDigitSpan.forbidden_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:04.479251+00:00
-- url     : https://prove2.me/submissions/18a4db85-f1cf-4605-a68e-0dd3e8b6f560

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_digitProjection_surjective
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_oldSpan_proper

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}
namespace ThreeSum.TernaryPhysicalDigitSpan
theorem _root_.solution (rows : List (Fin J → K)) (hlen : rows.length<J) : forbidden rows≠⊤ := by
  intro htop
  apply oldSpan_proper rows hlen
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := digitProjection_surjective (K := K) (J := J) v
  have hw : w∈forbidden rows := by rw [htop]; trivial
  exact hw
end ThreeSum.TernaryPhysicalDigitSpan
