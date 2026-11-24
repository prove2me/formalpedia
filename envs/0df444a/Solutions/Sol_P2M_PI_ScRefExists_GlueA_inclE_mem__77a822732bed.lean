-- Prove2me | solution 1 for P2M_PI_ScRefExists_GlueA_inclE_mem__77a822732bed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:40:20.902629+00:00
-- url     : https://prove2.me/submissions/d6f82723-151b-49bb-a5ea-799bf5b9fb3c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Theorems.Thm_PI_ScRefExists_GlueA_inclE_mem

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
theorem _root_.solution (t : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E) ∈ IntAf I.F I.E := inclE_mem I ⟨t, rfl⟩
end PI.ScRefExists.GlueA
