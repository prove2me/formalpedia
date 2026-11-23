-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_map_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:47.881804+00:00
-- url     : https://prove2.me/submissions/37ee32c8-d967-4600-9a8e-16c67ddb7310

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
theorem _root_.solution {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := ⟨(π g).toLinearMap, fun v => hπ.2.2.1 g v⟩
  exact f.inner_map_map x y
end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
