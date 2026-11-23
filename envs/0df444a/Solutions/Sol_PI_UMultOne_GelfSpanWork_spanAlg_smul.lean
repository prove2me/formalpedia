-- Prove2me | solution 1 for PI.UMultOne.GelfSpanWork.spanAlg_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:08.96546+00:00
-- url     : https://prove2.me/submissions/bab80610-9b11-43ad-9a63-0316aa82f580

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralSpanAlgebra_Burnside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.GelfSpanWork
open Matrix Module
variable {G : Type} [Group G] {N : ℕ}
namespace PI.UMultOne.GelfSpanWork
theorem _root_.solution (ρ : G →* GL (Fin N) ℂ) (a : spanAlg ρ) (v : Fin N → ℂ) :
    a • v = (a : Module.End ℂ (Fin N → ℂ)) v := rfl
end PI.UMultOne.GelfSpanWork
