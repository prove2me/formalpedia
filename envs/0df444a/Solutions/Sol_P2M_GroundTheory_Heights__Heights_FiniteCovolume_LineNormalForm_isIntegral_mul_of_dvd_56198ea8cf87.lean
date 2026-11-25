-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_mul_of_dvd_56198ea8cf87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:17.80719+00:00
-- url     : https://prove2.me/submissions/5a413b7d-97f7-46cb-897d-43c14d16167f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_isIntegral_natCast_mul_c5f7da338ffb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
variable {E : Type*} [Field E] [NumberField E]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
theorem _root_.solution {a b : ℕ} {x : E} (hx : IsIntegral ℤ ((a : E) * x)) (hab : a ∣ b) :
    IsIntegral ℤ ((b : E) * x) := by
  obtain ⟨k, rfl⟩ := hab
  have : ((a * k : ℕ) : E) * x = (k : E) * ((a : E) * x) := by push_cast; ring
  rw [this]
  exact isIntegral_natCast_mul hx
end GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
