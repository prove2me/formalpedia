-- Prove2me | solution 1 for PI.FJMA.freeOf_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:09.556375+00:00
-- url     : https://prove2.me/submissions/bcd663d3-695f-4c7a-a7da-d0eb88a463d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable {σ : Type}
namespace PI.FJMA
theorem _root_.solution {S T : Set σ} {G : MvPolynomial σ ℂ} (h1 : FreeOf S G) (h2 : FreeOf T G) :
    FreeOf (S ∪ T) G := by
  intro e he v hv
  rcases hv with hv | hv
  · exact h1 e he v hv
  · exact h2 e he v hv
end PI.FJMA
