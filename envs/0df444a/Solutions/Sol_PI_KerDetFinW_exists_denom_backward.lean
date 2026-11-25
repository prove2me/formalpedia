-- Prove2me | solution 1 for PI.KerDetFinW.exists_denom_backward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:59:44.300242+00:00
-- url     : https://prove2.me/submissions/7a71f5a5-9ed0-41bc-9954-7ca269c6d77f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
import Theorems.Thm_PI_KerDetFinW_exists_nat_mul_mem_frac_fam
import Theorems.Thm_PI_KerDetFinW_int_mul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) → ∀ a,
      (N : E) * g₀.symm v a ∈ I := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_frac_fam I hI
    (fun q : (Fin 4 × n) × Fin 4 => g₀.symm (Pi.single q.1 1) q.2)
  refine ⟨N, hN0, fun v hv a => ?_⟩
  have hv' : g₀.symm v = ∑ w, v w • g₀.symm (Pi.single w 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    rw [Pi.single_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hv', Finset.sum_apply, Finset.mul_sum, ← FractionalIdeal.mem_coe]
  refine Submodule.sum_mem _ fun w _ => ?_
  rw [FractionalIdeal.mem_coe, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
  exact int_mul_mem I (hv w) (hN (w, a))
end PI.KerDetFinW
