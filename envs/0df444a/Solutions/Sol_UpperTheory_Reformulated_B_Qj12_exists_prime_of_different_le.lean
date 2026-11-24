-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qj12.exists_prime_of_different_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:07.352159+00:00
-- url     : https://prove2.me/submissions/756b9dbb-690b-4eba-b2a3-c0fcfb2faf1f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPrimeOfDifferentLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
attribute [local instance] Subfield.toField._proof_1 SubfieldClass.toField._proof_12 SubringClass.toRing._proof_8
namespace UpperTheory.Reformulated.B.Qj12
theorem _root_.solution :
    ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥H.F)),
    differentIdeal ℤ (NumberField.RingOfIntegers ↥H.F) ≤ v.asIdeal →
      ∃ (p : ℕ),
        Nat.Prime p ∧
          p ∣ H.QS * H.q * H.d ∧
            (↑p : NumberField.RingOfIntegers ↥H.F) ∈
              v.asIdeal := by
  intro R H v h
  have h1 := h (Ideal.absNorm_mem _)
  rw [NumberField.absNorm_differentIdeal H.F] at h1
  have h0 : (NumberField.discr H.F).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.F)
  rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Multiset.prod_coe] at h1
  obtain ⟨x, hx, hxv⟩ := (v.isPrime.multiset_prod_mem_iff_exists_mem _).1 h1
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  refine ⟨p, hpp, H.der.discr_primes.1 p hpp ?_, hxv⟩
  rw [H.der.discr_sq]
  exact (Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactorsList hp)).trans (dvd_pow_self _ two_ne_zero)
end UpperTheory.Reformulated.B.Qj12
