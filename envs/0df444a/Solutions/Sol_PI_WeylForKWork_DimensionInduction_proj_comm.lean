-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.proj_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:32.243572+00:00
-- url     : https://prove2.me/submissions/42f612a7-8f0b-4f98-b2a8-9cab69383f58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_orth

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
theorem _root_.solution (hρ : Good ρ) {W : Submodule ℂ H} [FiniteDimensional ℂ W] (hW : Stab ρ W) :
    Comm ρ (W.starProjection : H →ₗ[ℂ] H) := by
  intro i v
  have hWo := stab_orth hρ hW
  show W.starProjection (ρ i v) = ρ i (W.starProjection v)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hW i _ (W.orthogonalProjection v).2
  · intro w hw
    rw [← map_sub]
    exact (Submodule.mem_orthogonal' W _).1 (hWo i _ (W.sub_starProjection_mem_orthogonal v)) w hw
end PI.WeylForKWork.DimensionInduction
