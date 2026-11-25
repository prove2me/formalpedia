-- Prove2me | solution 1 for PI.SelfDualLoc.W.ND.coe_mem_intOE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:16.89631+00:00
-- url     : https://prove2.me/submissions/6e60fbff-d11e-48fd-ae27-8a9dbde2359c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Nondeg
import Theorems.Thm_PI_SelfDualLoc_W_ND_mem_intOE_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W PI.SelfDualLoc.W.ND
open PI.SelfDualLoc
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.SelfDualLoc.W.ND
theorem _root_.solution (a : 𝓞 E) : (a : E) ∈ intOE E :=
  (mem_intOE_iff _).2 ⟨a, rfl⟩
end PI.SelfDualLoc.W.ND
