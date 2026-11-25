-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.Sand.urep_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:24.906246+00:00
-- url     : https://prove2.me/submissions/e1034d71-1fe1-40fb-9412-a408e92fefc5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_UrepMulApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_inner
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_Sand_urep_mul_apply

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
    ⟪π k u, v⟫_ℂ = ⟪u, π k⁻¹ v⟫_ℂ := by
  have h1 : π k (π k⁻¹ v) = v := by
    rw [← urep_mul_apply hπ, mul_inv_cancel, hπ.1, ContinuousLinearMap.one_apply]
  calc ⟪π k u, v⟫_ℂ = ⟪π k u, π k (π k⁻¹ v)⟫_ℂ := by rw [h1]
    _ = ⟪u, π k⁻¹ v⟫_ℂ := urep_inner hπ k u _
end PI.UnitaryGroupMassFormula.PhConvProj.Sand
