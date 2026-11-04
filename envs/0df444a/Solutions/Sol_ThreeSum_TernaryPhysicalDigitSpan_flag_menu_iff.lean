-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalDigitSpan.flag_menu_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:42.068287+00:00
-- url     : https://prove2.me/submissions/b63b2e5a-2bea-4f16-9e11-7f6fd9a038b5

import Definitions.Def_Submission_ThreeSum_LightStoredSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Theorems.Thm_ThreeSum_TernaryPhysicalDigitSpan_menu_admissible_iff

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
variable {K : Type*} [Field K] {J : ℕ}
variable {E : Type*} [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
variable {p : ℕ} [Fact p.Prime]
namespace ThreeSum.TernaryPhysicalDigitSpan
theorem _root_.solution [Algebra (ZMod p) E] (ℓ : E →ₗ[ZMod p] ZMod p) (rows : List (Fin J → ZMod p)) (seed : E×E) :
    LightStoredSpan.admissibleFlag (rows.map (reversal J))
      (physicalDigits (TernaryOriginalRowMenu.seedRow (J+2) ℓ seed))=1 ↔
      seed∈TernaryOriginalRowMenu.admissible (J+2) ℓ (forbidden rows) := by
  rw [LightStoredSpan.admissibleFlag_eq_one]
  exact (menu_admissible_iff ℓ rows seed).symm
end ThreeSum.TernaryPhysicalDigitSpan
