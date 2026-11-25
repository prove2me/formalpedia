-- Prove2me | solution 1 for PI.LocGlobInclWork.coe_pow_toNat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:50:37.448135+00:00
-- url     : https://prove2.me/submissions/62f042c0-c26b-49a1-aa05-f4d50e1567b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (k : ℤ) :
    ((v.asIdeal ^ k.toNat : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ k := by
  rw [FractionalIdeal.coeIdeal_pow]
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    simp
  · push_neg at hk
    obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hk.le
    have h0 : (-(n : ℤ)).toNat = 0 := Int.toNat_of_nonpos hk.le
    rw [h0, pow_zero, zpow_neg, zpow_natCast]
    have h1 : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n ≤ 1 := by
      rw [← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
    have h2 : (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n ≠ 0 :=
      pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1⁻¹ := inv_one.symm
      _ ≤ ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n)⁻¹ := FractionalIdeal.inv_anti_mono h2 one_ne_zero h1
end PI.LocGlobInclWork
