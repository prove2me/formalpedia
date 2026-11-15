-- Prove2me | solution 1 for PrimeLocal.local_package_componentFree
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:58:47.476485+00:00
-- url     : https://prove2.me/submissions/7f7569fb-6e63-48cf-8c0d-ac6331df1473

import Theorems.Thm_PrimeLocal_exists_global_integral_model_minimal_at_all_primes
import Theorems.Thm_PrimeLocal_transport_rational_point_to_integral_model
import Theorems.Thm_PrimeLocal_localClause_componentFree
import Theorems.Thm_PrimeLocal_atPrimeClause_componentFree
import Theorems.Thm_PrimeLocal_multiplicative_at_two_or_three
import Theorems.Thm_PrimeLocal_not_inZeroComponentAt_of_fixed_torsion_at_two_or_three
import Mathlib
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
theorem _root_.solution (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime) (h23 : 23 ≤ p) (P : (E⁄ℚ).Point) (hP : addOrderOf P = p) : ∃ (W : WeierstrassCurve ℤ) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), W.Δ ≠ 0 ∧ (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) ∧ addOrderOf Q = p ∧ (2:ℤ) ∣ W.Δ ∧ ¬ (2:ℤ) ∣ W.c₄ ∧ (3:ℤ) ∣ W.Δ ∧ ¬ (3:ℤ) ∣ W.c₄ ∧ (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ¬ W.InZeroComponentAt A Q) ∧ (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 → ¬ W.InZeroComponentAt A Q) ∧ (∀ q : ℕ, q.Prime → q ≠ p →
      ¬ (q : ℤ) ∣ W.Δ ∨ ((q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄) ∨
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y) ∧ ((¬ (p : ℤ) ∣ W.Δ ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ (x y : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          p • (Point.some x y h) = 0 ∧ x ∈ A)
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄)) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨W, C, hC, hΔ, hmin⟩ :=
    exists_global_integral_model_minimal_at_all_primes E
  obtain ⟨x, y, h, h', hP', hQord, hQfix⟩ :=
    transport_rational_point_to_integral_model E W C hC hΔ P hP hp
  let Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point :=
    Point.some _ _ h'
  have hloc := localClause_componentFree W hΔ hp (by omega) hmin
    x y h hP' Q hQfix hQord
  have hpat := atPrimeClause_componentFree W hΔ (hmin p) (by omega)
    x y h hP' Q hQfix hQord
  have htwo := multiplicative_at_two_or_three W hΔ (q := 2) (Or.inl rfl)
    (hmin 2) hp h23 x y h hP' Q hQfix hQord
  have hthree := multiplicative_at_two_or_three W hΔ (q := 3) (Or.inr rfl)
    (hmin 3) hp h23 x y h hP' Q hQfix hQord
  have htwoQ := not_inZeroComponentAt_of_fixed_torsion_at_two_or_three
    W hΔ Nat.prime_two (Or.inl rfl) htwo.1 htwo.2 hp (by omega)
    Q hQfix hQord
  have hthreeQ := not_inZeroComponentAt_of_fixed_torsion_at_two_or_three
    W hΔ Nat.prime_three (Or.inr rfl) hthree.1 hthree.2 hp (by omega)
    Q hQfix hQord
  exact ⟨W, Q, hΔ, hQfix, hQord, htwo.1, htwo.2, hthree.1, hthree.2,
    htwoQ, hthreeQ, hloc, hpat⟩
end PrimeLocal
