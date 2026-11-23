-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.stab_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:30.885326+00:00
-- url     : https://prove2.me/submissions/90569241-7456-4d78-b2c5-71abe5254ad5

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
theorem _root_.solution {ν : Sort*} {F : ν → Submodule ℂ H} (hF : ∀ k, Stab ρ (F k)) :
    Stab ρ (⨆ k, F k) := by
  intro i v hv
  have hle : (⨆ k, F k) ≤ (⨆ k, F k).comap (ρ i : H →ₗ[ℂ] H) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (hF k i x hx)
  exact hle hv
end PI.WeylForKWork.DimensionInduction
