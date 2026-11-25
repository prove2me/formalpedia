-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_chartRing_ptX_e1c6bdba4be9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:59.188556+00:00
-- url     : https://prove2.me/submissions/d5c71bc9-6ced-40a3-b005-5e240763452d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable (k : Type u) [Field k]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I : Chart (ptX k)) (a : k) : a ∈ chartRing k (ptX k) I :=
  ⟨C a, 1, 0, one_mem _, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman
