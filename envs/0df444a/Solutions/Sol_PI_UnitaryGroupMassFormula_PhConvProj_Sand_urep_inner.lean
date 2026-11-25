-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:10.036419+00:00
-- url     : https://prove2.me/submissions/f554fdab-268e-4273-8fc4-44e867c5823f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_UrepMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.Sand
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]
namespace PI.UnitaryGroupMassFormula.PhConvProj.Sand
theorem _root_.solution {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (k : G) (u v : K) :
    ⟪π k u, π k v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := { toLinearMap := (π k : K →ₗ[ℂ] K), norm_map' := hπ.2.2.1 k }
  exact f.inner_map_map u v
end PI.UnitaryGroupMassFormula.PhConvProj.Sand
