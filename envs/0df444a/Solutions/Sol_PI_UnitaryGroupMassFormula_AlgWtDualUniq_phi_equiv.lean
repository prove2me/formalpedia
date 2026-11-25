-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AlgWtDualUniq.phi_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:39.046831+00:00
-- url     : https://prove2.me/submissions/b32a7951-1262-4184-8fbe-9fe3ea4f0d96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightDualUniqueness_SelfInjective
import Theorems.Thm_PI_UnitaryGroupMassFormula_AlgWtDualUniq_phi_apply

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
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0) (g : G) (y : Vb) (x : Va) :
    phi B hB h0 (ρb g y) x = phi B hB h0 y (ρa g⁻¹ x) := by
  rw [phi_apply, phi_apply]
  have h1 := hB g (ρa g⁻¹ x) y
  rw [Representation.self_inv_apply] at h1
  exact h1
end PI.UnitaryGroupMassFormula.AlgWtDualUniq
