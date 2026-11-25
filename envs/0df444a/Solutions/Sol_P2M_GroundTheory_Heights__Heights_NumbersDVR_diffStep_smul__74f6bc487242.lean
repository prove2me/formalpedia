-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_smul__74f6bc487242
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:48.692184+00:00
-- url     : https://prove2.me/submissions/3041813b-cc70-4bfc-89a3-740f2980f173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear

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
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (b : K → ℤ) (c : ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (c • f) = c • diffStep b f := by
  funext m; simp only [diffStep, Pi.smul_apply, smul_eq_mul]; ring
end GroundTheory.Heights₂.Heights.NumbersDVR
