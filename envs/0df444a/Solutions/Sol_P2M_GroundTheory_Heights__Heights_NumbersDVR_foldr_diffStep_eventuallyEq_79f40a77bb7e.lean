-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_eventuallyEq_79f40a77bb7e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:14:40.396377+00:00
-- url     : https://prove2.me/submissions/8eb78216-ab21-4585-80f1-f672bc802d9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTClosure
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_eventuallyEq_a5803a6b204f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by
  induction l with
  | nil => simpa using h
  | cons b l ih =>
    simp only [List.foldr_cons]
    exact diffStep_eventuallyEq b ih
end GroundTheory.Heights₂.Heights.NumbersDVR
