-- Prove2me | solution 1 for PI.UMultOne.GelfSpanWork.repEnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:32:55.686107+00:00
-- url     : https://prove2.me/submissions/f1ec4744-adaf-4aff-9566-9599e62f1033

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
theorem _root_.solution (ρ : G →* GL (Fin N) ℂ) (g : G) (v : Fin N → ℂ) :
    repEnd ρ g v = ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v := by
  simp [repEnd, Matrix.toLin'_apply]
end PI.UMultOne.GelfSpanWork
