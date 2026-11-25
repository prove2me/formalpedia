-- Prove2me | solution 1 for PI.LocGlobInclWork.exists_unit_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:14:53.442812+00:00
-- url     : https://prove2.me/submissions/0bcdf98d-ca15-4325-b526-1f676c98df30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
import Theorems.Thm_PI_LocGlobInclWork_coe_prod_le

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hw : w ∉ S) (n : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ t : 𝓞 K, t ∉ w.asIdeal ∧
      algebraMap (𝓞 K) K t ∈ ∏ v ∈ S, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n v := by
  classical
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hP : ¬ (∏ v ∈ S, v.asIdeal ^ (n v).toNat) ≤ w.asIdeal := by
    intro hle
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      rw [Finset.prod_empty, Ideal.one_eq_top] at hle
      exact w.isPrime.ne_top (top_le_iff.mp hle)
    · obtain ⟨v, hv, hvle⟩ := (Ideal.IsPrime.prod_le w.isPrime).mp hle
      have h1 : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le hvle
      have h2 : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top h1
      have h3 : v = w := IsDedekindDomain.HeightOneSpectrum.ext h2
      exact hw (h3 ▸ hv)
  obtain ⟨t, htP, htw⟩ := SetLike.not_le_iff_exists.mp hP
  refine ⟨t, htw, ?_⟩
  exact coe_prod_le S n ((FractionalIdeal.mem_coeIdeal _).mpr ⟨t, htP, rfl⟩)
end PI.LocGlobInclWork
