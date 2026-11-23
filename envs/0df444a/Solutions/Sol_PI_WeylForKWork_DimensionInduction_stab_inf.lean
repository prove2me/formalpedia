-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.stab_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:31.173305+00:00
-- url     : https://prove2.me/submissions/53a539f8-27bf-4198-9bbd-55ae4fac726c

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
theorem _root_.solution {W W' : Submodule ℂ H} (h : Stab ρ W) (h' : Stab ρ W') : Stab ρ (W ⊓ W') := by
  intro i v hv
  exact ⟨h i v hv.1, h' i v hv.2⟩
end PI.WeylForKWork.DimensionInduction
