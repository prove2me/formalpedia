-- Prove2me | solution 1 for ValuationSubring.exists_isFrobeniusAt_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3c9711bc-37ff-5a09-905b-02ef8e78df90

import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_rat

theorem solution (ℓ : ℕ) (hℓ : ℓ.Prime) : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧ ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ := by
  classical
  let O : Subalgebra ℤ (AlgebraicClosure ℚ) := integralClosure ℤ (AlgebraicClosure ℚ)

  have hℓZ : Prime (ℓ : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ)
  haveI hPmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hℓZ.irreducible

  have hker : RingHom.ker (algebraMap ℤ O) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ O).injective_int]
    exact bot_le
  obtain ⟨𝔔, h𝔔max, h𝔔⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := O) (Ideal.span {(ℓ : ℤ)}) hker
  have hℓ𝔔 : (ℓ : O) ∈ 𝔔 := by
    have h : (ℓ : ℤ) ∈ Ideal.comap (algebraMap ℤ O) 𝔔 := by
      rw [h𝔔]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using h

  obtain ⟨A, -, h𝔔A⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := O.toSubring) 𝔔 h𝔔max.ne_top
  have hA : A.LiesOverPrime ℓ := by
    have h : ((ℓ : O) : AlgebraicClosure ℚ) ∈ A.nonunits := h𝔔A ⟨(ℓ : O), hℓ𝔔, rfl⟩
    simp at h
    exact h
  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hℓ A hA
  exact ⟨A, hA, φ, hφ⟩

end S_ValuationSubring_exists_isFrobeniusAt_rat
end P2MW
export P2MW.S_ValuationSubring_exists_isFrobeniusAt_rat (solution)
