-- Prove2me | solution 1 for UpperTheory.Ram.not_dvd_QS_of_notMem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:08:05.956038+00:00
-- url     : https://prove2.me/submissions/13d0d2c0-a28a-4cdf-ac35-869941c02e69

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_NotSmallIso
import Theorems.Thm_Formalism_HC_HostAx_mem_sq_of_dvd_QS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace UpperTheory.Ram
theorem _root_.solution :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), H.toHostRaw.Exact → ∀ (E' : Type) [Field E'] [NumberField E'] (_ : E' ≃+* H.E) (P : HeightOneSpectrum (𝓞 E')) (p : ℕ), p.Prime →
      (p : 𝓞 E') ∈ P.asIdeal → (p : 𝓞 E') ∉ P.asIdeal ^ 2 → ¬ p ∣ H.QS ∧ (H.QS : 𝓞 E') ∉ P.asIdeal := by
  intro φ H hex E' _ _ f P p hp hpP hpP2
  haveI hPp : P.asIdeal.IsPrime := P.isPrime
  let g : 𝓞 H.E ≃+* 𝓞 E' := (NumberField.RingOfIntegers.mapRingEquiv f).symm
  let Q : Ideal (𝓞 H.E) := P.asIdeal.comap g
  haveI : Q.IsPrime := Ideal.comap_isPrime g P.asIdeal
  have hndvd : ¬ p ∣ H.QS := by
    intro hdvd
    have hmem : ((p : ℕ) : 𝓞 H.E) ∈ Q := by
      show g (p : 𝓞 H.E) ∈ P.asIdeal
      rw [map_natCast]
      exact hpP
    have h2 := H.mem_sq_of_dvd_QS hex hp hdvd Q hmem
    have h3 : g (p : 𝓞 H.E) ∈ P.asIdeal ^ 2 := Ideal.le_comap_pow g 2 h2
    rw [map_natCast] at h3
    exact hpP2 h3
  refine ⟨hndvd, fun hQS => ?_⟩
  have hcop : p.Coprime H.QS := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hb := Nat.gcd_eq_gcd_ab p H.QS
  rw [hcop.gcd_eq_one] at hb
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 := congrArg (Int.cast : ℤ → 𝓞 E') hb
  push_cast at h1
  rw [h1]
  exact add_mem (P.asIdeal.mul_mem_right _ hpP) (P.asIdeal.mul_mem_right _ hQS)
end UpperTheory.Ram
