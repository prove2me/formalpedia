-- Prove2me | solution 1 for PI.AdCpctDenWork.exists_nat_adele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:07.137922+00:00
-- url     : https://prove2.me/submissions/ed01aa5a-5d08-4b2c-a97a-ad01a5240f90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
import Theorems.Thm_PI_AdCpctDenWork_natCast_mul_apply
import Theorems.Thm_PI_AdCpctDenWork_natCast_mem_int
import Theorems.Thm_PI_AdCpctDenWork_exists_nat_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AdCpctDenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
namespace PI.AdCpctDenWork
theorem _root_.solution (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ (n : FiniteAdeleRing (𝓞 F) F) * a ∈ intAd F := by
  classical
  choose m hm0 hm using fun v => exists_nat_local (F := F) v (a v)
  have hS : {v : HeightOneSpectrum (𝓞 F) | ¬ a v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp a.2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [natCast_mul_apply]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.adicCompletion F), mul_assoc]
    exact mul_mem (natCast_mem_int w k) (hm w)
  · have hw' : a w ∈ w.adicCompletionIntegers F := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem_int w _) hw'
end PI.AdCpctDenWork
