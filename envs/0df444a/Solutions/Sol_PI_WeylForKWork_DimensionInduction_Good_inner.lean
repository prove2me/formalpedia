-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.Good.inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:30.631911+00:00
-- url     : https://prove2.me/submissions/f0af0bc6-28c0-44be-8ce9-a097d5bd3ef3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}
variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
namespace PI.WeylForKWork.DimensionInduction
namespace Good
theorem _root_.solution (hρ : Good ρ) (i : ι) (x y : H) : ⟪ρ i x, ρ i y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ i : H →ₗ[ℂ] H), hρ.isom i⟩
  exact L.inner_map_map x y
end Good
end PI.WeylForKWork.DimensionInduction
