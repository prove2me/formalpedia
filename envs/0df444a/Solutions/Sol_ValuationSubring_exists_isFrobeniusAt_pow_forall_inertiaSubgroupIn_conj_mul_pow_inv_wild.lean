-- Prove2me | solution 1 for ValuationSubring.exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/43c2135b-05a0-5203-a7c5-870f15b8b106

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime
import Theorems.Thm_TWLoc_frobenius_conj_mul_pow_inv_wild
import Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] :
    ∃ (d : ℕ) (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), 0 < d ∧ (∀ z ∈ K, φ z = z) ∧
      A.IsFrobeniusAt φ (p ^ d) ∧
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ →
        φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹ ∈ A.inertiaSubgroupIn ℚ ∧
        (∀ z : AlgebraicClosure ℚ, z ≠ 0 →
          (φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) z * z⁻¹ - 1 ∈ A.nonunits) ∧
        ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F],
          ∃ a : ℕ, ∀ x ∈ F, ((φ * τ * φ⁻¹ * (τ ^ (p ^ d))⁻¹) ^ (p ^ a)) x = x := by
  obtain ⟨d, φ, hd, -, hfix, hφ⟩ :=
    ValuationSubring.exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime p A hA K
  refine ⟨d, φ, hd, hfix, hφ, fun τ hτ => ?_⟩
  obtain ⟨hmem, hwild⟩ := TWLoc.frobenius_conj_mul_pow_inv_wild (q := p ^ d) A hφ hτ
  refine ⟨hmem, hwild, fun F _ _ => ?_⟩
  exact ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild (Fact.out : p.Prime) A hA hwild F

end S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild
end P2MW
export P2MW.S_ValuationSubring_exists_isFrobeniusAt_pow_forall_inertiaSubgroupIn_conj_mul_pow_inv_wild (solution)
