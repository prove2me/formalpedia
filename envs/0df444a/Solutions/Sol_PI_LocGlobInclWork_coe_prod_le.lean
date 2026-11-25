-- Prove2me | solution 1 for PI.LocGlobInclWork.coe_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:54.312864+00:00
-- url     : https://prove2.me/submissions/67649d9f-c181-43c7-85e2-df8a416b4c4b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
import Theorems.Thm_PI_LocGlobInclWork_coe_pow_toNat_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
namespace PI.LocGlobInclWork
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ((∏ v ∈ S, v.asIdeal ^ (n v).toNat : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      ∏ v ∈ S, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert v S hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv, FractionalIdeal.coeIdeal_mul]
    rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
    have h1 := FractionalIdeal.coe_le_coe.mpr (coe_pow_toNat_le v (n v))
    have h2 := FractionalIdeal.coe_le_coe.mpr ih
    first
      | exact mul_le_mul' h1 h2
      | exact Submodule.mul_le_mul' h1 h2
      | exact Submodule.mul_le_mul_of_le_of_le h1 h2
end PI.LocGlobInclWork
