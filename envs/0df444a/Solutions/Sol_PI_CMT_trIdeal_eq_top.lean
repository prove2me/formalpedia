-- Prove2me | solution 1 for PI.CMT.trIdeal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:40.851605+00:00
-- url     : https://prove2.me/submissions/15eb9ec9-b386-4410-b05b-e3585d919a03

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Theorems.Thm_PI_CMT_coe_conj
import Theorems.Thm_PI_CMT_conj_conj
import Theorems.Thm_PI_CMT_isTr_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
namespace PI.CMT
theorem _root_.solution
    (hP : ∀ P : Ideal (𝓞 K), P.IsMaximal →
      ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    trIdeal K = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hnot⟩ := hP P hPmax
  have htc : t = conj θ := by
    apply RingOfIntegers.ext
    rw [coe_conj]
    exact ht
  rw [htc] at hnot
  have h1 : θ + conj θ ∈ P :=
    hle (Ideal.subset_span (isTr_self θ))
  have h2 : θ * conj θ + conj (θ * conj θ) ∈ P :=
    hle (Ideal.subset_span (isTr_self _))
  have h3 : (θ - conj θ) ^ 2 ∈ P := by
    have e : (θ - conj θ) ^ 2 =
        (θ + conj θ) * (θ + conj θ) -
          2 * (θ * conj θ + conj (θ * conj θ)) := by
      rw [map_mul, conj_conj]
      ring
    rw [e]
    exact P.sub_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)
  exact hnot (hPmax.isPrime.mem_of_pow_mem 2 h3)
end PI.CMT
