-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:54.060421+00:00
-- url     : https://prove2.me/submissions/e71f1b44-170d-40c2-8919-c484b3c5cf7c

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qm7_exists_common_multiple__e387a76b269a
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
omit [Field E] [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
theorem _root_.solution {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (hP : ∀ i a b, P i a → a ∣ b → P i b) (hex : ∀ i ∈ s, ∃ a, 0 < a ∧ P i a) :
    ∃ d, 0 < d ∧ ∀ i ∈ s, P i d :=
  _root_.P2M_UpperTheory_Reformulated_B_Qm7_exists_common_multiple__e387a76b269a s P hP hex
end GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
