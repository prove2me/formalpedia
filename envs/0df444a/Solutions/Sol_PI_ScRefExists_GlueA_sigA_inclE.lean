-- Prove2me | solution 1 for PI.ScRefExists.GlueA.sigA_inclE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:17:31.308549+00:00
-- url     : https://prove2.me/submissions/36193f03-bbbf-45ae-9ead-d120d239704a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Theorems.Thm_PI_ScRefExists_GlueA_inclE_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GlueA
theorem _root_.solution (a : I.E) :
    sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) a) = Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
  rw [inclE_tmul, inclE_tmul]
  first
    | exact Algebra.TensorProduct.map_tmul _ _ _ _
    | rfl
end PI.ScRefExists.GlueA
