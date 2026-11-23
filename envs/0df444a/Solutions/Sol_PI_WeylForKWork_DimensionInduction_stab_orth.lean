-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.stab_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:31.093735+00:00
-- url     : https://prove2.me/submissions/fc6b4529-bc8c-4314-8874-f584f49b0ef5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_Good_inner

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
theorem _root_.solution (hρ : Good ρ) {W : Submodule ℂ H} (hW : Stab ρ W) : Stab ρ Wᗮ := by
  intro i v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro w hw
  obtain ⟨j, hj⟩ := hρ.inv i
  rw [← hj w, hρ.inner i]
  exact hv _ (hW j w hw)
end PI.WeylForKWork.DimensionInduction
