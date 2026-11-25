-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_mem_intMultiples_818cdd960c3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:51.757914+00:00
-- url     : https://prove2.me/submissions/119ad7bc-f7eb-472b-b0b1-646813adb62b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm

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
theorem _root_.solution {N : ℕ} {x : E} : x ∈ intMultiples E N ↔ IsIntegral ℤ ((N : E)⁻¹ * x) :=
  Iff.rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
