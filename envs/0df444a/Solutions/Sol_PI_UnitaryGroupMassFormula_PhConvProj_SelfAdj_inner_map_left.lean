-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.inner_map_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:38.529519+00:00
-- url     : https://prove2.me/submissions/0d53b60d-e3be-46f9-991e-ebb72c48627c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_SelfAdj
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_inner_map_map
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhConvProj_SelfAdj_map_inv_map

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
    ⟪π g x, y⟫_ℂ = ⟪x, π g⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← (map_inv_map hπ) g y]
  exact (inner_map_map hπ) g x (π g⁻¹ y)
end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
