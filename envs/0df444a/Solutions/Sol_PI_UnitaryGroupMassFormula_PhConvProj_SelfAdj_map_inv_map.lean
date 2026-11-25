-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.map_inv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:13.741795+00:00
-- url     : https://prove2.me/submissions/b8f26375-3a9e-4486-9555-82696a28d108

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_SelfAdj

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhConvProj PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
open PI.PhConvProj
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
namespace PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
theorem _root_.solution {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (y : K) :
    π g (π g⁻¹ y) = y := by
  have h := congrArg (fun A : K →L[ℂ] K => A y) (hπ.2.1 g g⁻¹)
  simp only [mul_inv_cancel, hπ.1, ContinuousLinearMap.coe_comp, Function.comp_apply] at h
  rw [← h]
  rfl
end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
