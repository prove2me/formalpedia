-- Prove2me | solution 1 for PI.Dv.GLP.exists_end_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:28.08944+00:00
-- url     : https://prove2.me/submissions/fbce6205-f355-4f8e-93ee-56d40f67f993

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {x : W} (hx : x ≠ 0) (y : W) : ∃ b : Module.End K W, b x = y := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff K x).1 h)
  refine ⟨(φ x)⁻¹ • LinearMap.smulRight φ y, ?_⟩
  simp [LinearMap.smulRight_apply, smul_smul, inv_mul_cancel₀ hφ]
end PI.Dv.GLP
