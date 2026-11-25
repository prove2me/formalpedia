-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AlgWtDualUniq.dual_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:30.985242+00:00
-- url     : https://prove2.me/submissions/5e63696d-a970-4871-af23-9eaaf9c53046

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightDualUniqueness_SelfInjective
import Theorems.Thm_PI_UnitaryGroupMassFormula_AlgWtDualUniq_phi_equiv

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
theorem _root_.solution {Vc : Type*} [AddCommGroup Vc] [Module ℂ Vc] {ρc : Representation ℂ G Vc}
    [FiniteDimensional ℂ Va] [FiniteDimensional ℂ Vb] [FiniteDimensional ℂ Vc]
    [ρa.IsIrreducible] [ρb.IsIrreducible] [ρc.IsIrreducible]
    (B : Va →ₗ[ℂ] Vb →ₗ[ℂ] ℂ) (hB : Inv ρa ρb B) (h0 : B ≠ 0)
    (C : Va →ₗ[ℂ] Vc →ₗ[ℂ] ℂ) (hC : Inv ρa ρc C) (hC0 : C ≠ 0) :
    ∃ T : Vb ≃ₗ[ℂ] Vc, ∀ g y, T (ρb g y) = ρc g (T y) := by
  refine ⟨(phi B hB h0).trans (phi C hC hC0).symm, fun g y => ?_⟩
  apply (phi C hC hC0).injective
  ext x
  rw [phi_equiv C hC hC0 g]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [phi_equiv B hB h0 g]
end PI.UnitaryGroupMassFormula.AlgWtDualUniq
