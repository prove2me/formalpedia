-- Prove2me | solution 1 for PrimeLocal.localClause_componentFree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:40:52.973265+00:00
-- url     : https://prove2.me/submissions/93966ee7-65f8-46cf-b3fd-6f58c6aa6949

import Mathlib
import Theorems.Thm_PrimeLocal_not_dvd_discr_iff_hasGoodReduction
import Theorems.Thm_PrimeLocal_dvd_discr_and_not_dvd_c4_iff_hasMultiplicativeReduction
import Theorems.Thm_PrimeLocal_dvd_discr_and_dvd_c4_iff_hasAdditiveReduction
import Theorems.Thm_PrimeLocal_inertia_fixed_primePower_of_potentiallyGood_fixed_point
import Theorems.Thm_PrimeLocal_no_additive_nonintegral_j_of_fixed_prime_torsion
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmin : ∀ (q : ℕ) [Fact q.Prime], WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : (∀ q : ℕ, q.Prime → q ≠ p →
      ¬ (q : ℤ) ∣ W.Δ ∨ ((q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄) ∨
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y) := by
  intro q hq hqp
  letI : Fact q.Prime := ⟨hq⟩
  letI : WeierstrassCurve.IsMinimal ℤ_[q]
      (W.map (Int.castRingHom ℚ_[q])) := hmin q
  rcases (W.map (Int.castRingHom ℚ_[q])).hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction ℤ_[q] with hg | hm | ha
  · exact Or.inl ((PrimeLocal.not_dvd_discr_iff_hasGoodReduction W q).mp hg)
  · exact Or.inr (Or.inl
      ((PrimeLocal.dvd_discr_and_not_dvd_c4_iff_hasMultiplicativeReduction W q).mp hm))
  · obtain ⟨hqΔ, hqc₄⟩ :=
      (PrimeLocal.dvd_discr_and_dvd_c4_iff_hasAdditiveReduction W q).mp ha
    by_cases hj : (q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3
    · exact Or.inr (Or.inr
        (PrimeLocal.inertia_fixed_primePower_of_potentiallyGood_fixed_point
          W hΔ hp hp5 hq hqp hj Q hQfix hQord))
    · exact (PrimeLocal.no_additive_nonintegral_j_of_fixed_prime_torsion
        W hΔ (hmin q) hp hp5 hqp hqΔ hqc₄ hj x y h hP).elim
end PrimeLocal
