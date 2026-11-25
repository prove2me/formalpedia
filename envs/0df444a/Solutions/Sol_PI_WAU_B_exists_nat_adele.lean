-- Prove2me | solution 1 for PI.WAU.B.exists_nat_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:12:25.079177+00:00
-- url     : https://prove2.me/submissions/a882fbc9-2b45-4784-bc6a-845de7253438

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Theorems.Thm_PI_WAU_B_natCast_mul_apply
import Theorems.Thm_PI_WAU_B_exists_nat_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.WAU.B
theorem _root_.solution (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ ∀ v, ((n : FiniteAdeleRing (𝓞 F) F) * a) v ∈ v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 a.2
  choose N hNpos hN using fun v => exists_nat_local v (a v)
  refine ⟨∏ v ∈ hfin.toFinset, N v, Finset.prod_pos fun v _ => hNpos v, fun v => ?_⟩
  rw [natCast_mul_apply]
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv, Nat.cast_mul, mul_comm ((N v : ℕ) : v.adicCompletion F),
      mul_assoc]
    exact mul_mem (natCast_mem _ _) (hN v)
  · have hav : a v ∈ v.adicCompletionIntegers F := by
      by_contra hc
      exact hv (hfin.mem_toFinset.2 hc)
    exact mul_mem (natCast_mem _ _) hav
end PI.WAU.B
