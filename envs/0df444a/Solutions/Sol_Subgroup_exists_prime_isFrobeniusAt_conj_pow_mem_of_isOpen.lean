-- Prove2me | solution 1 for Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f45dd2b9-cdce-56c8-8f43-4568945caf1d

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_IsOpen_exists_numberField_ker_restrictNormalHom_le
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

theorem solution
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H := by

  obtain ⟨F, hF, hNF, hGal, hAlg, hST, hker⟩ :=
    hH.exists_numberField_ker_restrictNormalHom_le
  letI := hF; letI := hNF; letI := hGal; letI := hAlg; letI := hST

  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS, hA, hτ, hmem⟩ :=
    FrobeniusDensity.frobeniusPowerDense_of_le_ker F hker M.primeFactors σ

  exact ⟨ℓ, A, τ, g, n, hℓ,
    fun hdvd => hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hM.ne'⟩),
    hA, hτ, hmem⟩

end S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
end P2MW
export P2MW.S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen (solution)
