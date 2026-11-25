-- Prove2me | solution 1 for PI.UMultOne.GelfSpanWork.repEnd_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:03.223021+00:00
-- url     : https://prove2.me/submissions/538ba903-0e0d-4c2e-9a94-96473aa492d1

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
theorem _root_.solution (ρ : G →* GL (Fin N) ℂ) (g : G) : repEnd ρ g ∈ spanAlg ρ :=
  Algebra.subset_adjoin ⟨g, rfl⟩
end PI.UMultOne.GelfSpanWork
