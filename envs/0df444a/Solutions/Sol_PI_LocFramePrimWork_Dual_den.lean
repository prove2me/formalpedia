-- Prove2me | solution 1 for PI.LocFramePrimWork.Dual_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:10.132097+00:00
-- url     : https://prove2.me/submissions/2743206b-e3d9-407b-9c7a-9792cc75d784

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution {ι : Type} [Fintype ι] (g : ι → Fin n → E) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Set.range g)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ o : ι → 𝓞 E, (d : E) • y = ∑ i, (o i : E) • g i := by
  classical
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ c
  choose o ho using fun i => hb i (Finset.mem_univ i)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, o, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  have h := ho i
  rw [Algebra.smul_def] at h
  exact h.symm
end PI.LocFramePrimWork
