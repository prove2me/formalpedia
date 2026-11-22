-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.stab_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:24.459167+00:00
-- url     : https://prove2.me/submissions/b00b0d13-e1d9-4852-a7bd-d2b99bf8ec07

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
theorem _root_.solution {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hX : Stab ρ X) :
    Stab ρ (X.map c) := by
  rintro i _ ⟨x, hx, rfl⟩
  exact ⟨ρ i x, hX i x hx, hc i x⟩
end PI.WeylForKWork.DimensionInduction
