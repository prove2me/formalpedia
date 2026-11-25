-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AlgWtDualUniq.phi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:37.81938+00:00
-- url     : https://prove2.me/submissions/e62f1dcb-369a-490e-9212-485dbf962cb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightDualUniqueness_SelfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AlgWtDualUniq
open Module
variable {G : Type*} [Group G] {Va Vb : Type*} [AddCommGroup Va] [Module ℂ Va] [AddCommGroup Vb] [Module ℂ Vb]
  (ρa : Representation ℂ G Va) (ρb : Representation ℂ G Vb)
variable {ρa ρb}
namespace PI.UnitaryGroupMassFormula.AlgWtDualUniq
theorem _root_.solution [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [ρa.IsIrreducible] [ρb.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) (y : Vb) (x : Va) :
    phi B hB h0 y x = B x y := rfl
end PI.UnitaryGroupMassFormula.AlgWtDualUniq
