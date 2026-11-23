-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhSchurConv.Main.inner_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:09.511391+00:00
-- url     : https://prove2.me/submissions/fb4f07c0-83b3-40af-864b-906b0a7db92d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhSchurConv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurConvolution_MapMulApply

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhSchurConv PI.UnitaryGroupMassFormula.PhSchurConv.Main
open PI.PhSchurConv
namespace PI.UnitaryGroupMassFormula.PhSchurConv.Main
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (a b : H) : ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hU.2.2.1 g⟩
  exact L.inner_map_map a b
end PI.UnitaryGroupMassFormula.PhSchurConv.Main
