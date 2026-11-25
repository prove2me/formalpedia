-- Prove2me | solution 1 for PositivityTheory.ThKG.CayleyTransformDarboux.low_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:25.395077+00:00
-- url     : https://prove2.me/submissions/8e5a3917-896b-4e10-9a0f-0f77c29ef16f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreMain
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ToralCohomology_ShiftLow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action PositivityTheory.KReal
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.CayleyTransformDarboux
variable {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.ThKG.CayleyTransformDarboux
theorem _root_.solution {M' : Type} [AddCommGroup M'] [Module ℂ M'] {T : Module.End ℂ M} {lam : ℂ} (D : M →ₗ[ℂ] M')
    (hD : ∀ x, D (T x) = lam • D x) : low T lam ≤ LinearMap.ker D := by
  refine iSup_le fun t x hx => ?_
  rw [Module.End.mem_eigenspace_iff] at hx
  have := hD x
  rw [hx, map_smul, sub_smul, sub_eq_self, smul_eq_zero] at this
  exact this.resolve_left (by exact_mod_cast t.2.ne')
end PositivityTheory.ThKG.CayleyTransformDarboux
