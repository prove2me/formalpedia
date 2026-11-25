-- Prove2me | solution 1 for PI.Dv.TIW.trace_mem_of_intR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:51.846596+00:00
-- url     : https://prove2.me/submissions/cb7cc829-4468-4310-b161-42f4f28a27a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Theorems.Thm_PI_Dv_TIW_intEl_of_intR
import Theorems.Thm_PI_Dv_TIW_trace_tau_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)
namespace PI.Dv.TIW
theorem _root_.solution (z : MonoidAlgebra K G) (hz : IntR z) :
    LinearMap.trace K W (τ.asAlgebraHom z) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hz' := intEl_of_intR z hz
  have key : LinearMap.trace K W (τ.asAlgebraHom z) ∈ (algebraMap (𝓞 K) K).range := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum, map_sum]
    refine Subring.sum_mem _ fun g _ => ?_
    rw [map_smul, smul_eq_mul]
    exact Subring.mul_mem _ (RingHom.mem_range.mpr (hz' g)) (RingHom.mem_range.mpr (trace_tau_mem τ g))
  exact RingHom.mem_range.mp key
end PI.Dv.TIW
