-- Prove2me | solution 1 for PI.SelfDualLoc.W.sigR_inclE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:59.299566+00:00
-- url     : https://prove2.me/submissions/9f71437b-c521-4e54-acc3-8fb5528adcab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Theorems.Thm_PI_SelfDualLoc_W_sigR_tmul
import Theorems.Thm_PI_SelfDualLoc_W_inclE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace PI.SelfDualLoc.W
theorem _root_.solution (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR σ R (inclE R e) = inclE R (σ e) := by
  rw [inclE_apply, inclE_apply, sigR_tmul]
end PI.SelfDualLoc.W
