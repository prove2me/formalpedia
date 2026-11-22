-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.comm_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:22.53656+00:00
-- url     : https://prove2.me/submissions/7b59f2de-2783-46ff-8ca5-0a069dea4689

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
theorem _root_.solution {c d : H →ₗ[ℂ] H} (hc : Comm ρ c) (hd : Comm ρ d) : Comm ρ (c ∘ₗ d) := by
  intro i v
  show c (d (ρ i v)) = ρ i (c (d v))
  rw [hd i v, hc i (d v)]
end PI.WeylForKWork.DimensionInduction
