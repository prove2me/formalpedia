-- Prove2me | solution 1 for UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:01.28687+00:00
-- url     : https://prove2.me/submissions/33a6b81a-8226-4f9b-b9a4-e5666f838a37

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_CmDatumNatCastMemHeightOneSpectrumIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Formalism.HC IsDedekindDomain
private theorem natCast_mem_iff (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ((n : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∣ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]
private theorem ringChar_prime (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (ringChar (𝓞 K ⧸ la.asIdeal)).Prime := by
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot la.asIdeal la.ne_bot
  exact CharP.char_prime_of_ne_zero (𝓞 K ⧸ la.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
end

set_option autoImplicit false
open NumberField Formalism.HC IsDedekindDomain
namespace UpperTheory
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostRaw φ) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)),
      (((H.QS : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∈ H.small) ∧
      (((H.condN : ℕ) : 𝓞 K) ∈ la.asIdeal ↔ ringChar (𝓞 K ⧸ la.asIdeal) ∣ H.condN) := by
  intro φ H K _ _ la
  refine ⟨?_, natCast_mem_iff K la _⟩
  rw [natCast_mem_iff]
  exact ⟨fun h => Nat.mem_primeFactors.2 ⟨ringChar_prime K la, h, H.QS_pos.ne'⟩,
    fun h => Nat.dvd_of_mem_primeFactors h⟩
end UpperTheory
