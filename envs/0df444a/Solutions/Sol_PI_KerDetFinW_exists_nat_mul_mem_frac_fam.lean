-- Prove2me | solution 1 for PI.KerDetFinW.exists_nat_mul_mem_frac_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:47.347465+00:00
-- url     : https://prove2.me/submissions/850878ff-0c5d-49fe-b1c5-f20da35f4b45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Theorems.Thm_PI_KerDetFinW_nat_mul_mem
import Theorems.Thm_PI_KerDetFinW_exists_nat_mul_mem_frac

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
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ N : ℕ, 0 < N ∧ ∀ i, (N : E) * f i ∈ I := by
  choose d hd0 hd using fun i => exists_nat_mul_mem_frac I hI (f i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd0 i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hc, Nat.cast_mul, mul_comm (d i : E), mul_assoc]
  exact nat_mul_mem I c (hd i)
end PI.KerDetFinW
