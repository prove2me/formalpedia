-- Prove2me | solution 1 for PrimeLocal.atPrimeClause_componentFree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:58:46.636432+00:00
-- url     : https://prove2.me/submissions/c2544dae-c091-4a0e-9794-f4238e176bc6

import Mathlib
import Theorems.Thm_PrimeLocal_rational_point_supplies_atP_hord
import Theorems.Thm_PrimeLocal_no_additive_integral_j_at_p
import Theorems.Thm_PrimeLocal_exists_global_multiplicative_ramifiedTwist_at_p
import Theorems.Thm_PrimeLocal_no_signed_point_of_multiplicative_at_p
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
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) (hp17 : 17 ≤ p) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ((¬ (p : ℤ) ∣ W.Δ ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ (x y : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          p • (Point.some x y h) = 0 ∧ x ∈ A)
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by omega
  by_cases hpΔ : (p : ℤ) ∣ W.Δ
  · by_cases hpc₄ : (p : ℤ) ∣ W.c₄
    · by_cases hj : (p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3
      · exact (PrimeLocal.no_additive_integral_j_at_p
          W hΔ hmin hp17 hpΔ hpc₄ hj x y h hP).elim
      · obtain ⟨W', Q', s, hs, hΔ', hpΔ', hpc₄', hQ', hsign⟩ :=
          PrimeLocal.exists_global_multiplicative_ramifiedTwist_at_p
            W hΔ hmin hp5 hpΔ hpc₄ hj Q hQfix hQord
        exact (PrimeLocal.no_signed_point_of_multiplicative_at_p
          W' hΔ' hp hp5 hpΔ' hpc₄' Q' hQ' s hs hsign).elim
    · exact Or.inr ⟨hpΔ, hpc₄⟩
  · exact Or.inl ⟨hpΔ, PrimeLocal.rational_point_supplies_atP_hord
      W hΔ hp (by omega) x y h hP⟩
end PrimeLocal
