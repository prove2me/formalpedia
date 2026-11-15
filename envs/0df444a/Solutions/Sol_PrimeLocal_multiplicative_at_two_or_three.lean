-- Prove2me | solution 1 for PrimeLocal.multiplicative_at_two_or_three
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:29:30.506827+00:00
-- url     : https://prove2.me/submissions/b3d5f54c-cf44-4d29-82ca-3aa83994f43d

import Mathlib
import Theorems.Thm_PrimeLocal_no_fixed_prime_torsion_of_integral_j
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
/-- Integral-j and additive nonintegral-j exclusions force multiplicative reduction at two and three. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p q : ℕ} [Fact q.Prime] (hq23 : q = 2 ∨ q = 3) (hmin : WeierstrassCurve.IsMinimal ℤ_[q] (W.map (Int.castRingHom ℚ_[q]))) (hp : p.Prime) (hp23 : 23 ≤ p) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : (q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄ := by
  have hqle : q ≤ 3 := by
    rcases hq23 with hq | hq <;> omega
  have hqp : q ≠ p := by omega
  have hcount : 2 * q < p - 1 := by omega
  have hj : ¬ ((q : ℤ) ^ padicValInt q W.Δ ∣ W.c₄ ^ 3) := by
    intro hj
    exact no_fixed_prime_torsion_of_integral_j W hΔ hp (Fact.out : q.Prime)
      hqp hcount hj Q hQfix hQord
  have hqΔ : (q : ℤ) ∣ W.Δ := by
    by_cases hd : (q : ℤ) ∣ W.Δ
    · exact hd
    · apply False.elim
      apply hj
      rw [padicValInt.eq_zero_of_not_dvd hd]
      simp
  refine ⟨hqΔ, ?_⟩
  intro hqc₄
  exact no_additive_nonintegral_j_of_fixed_prime_torsion W hΔ hmin hp
    (by omega) hqp hqΔ hqc₄ hj x y h hP
end PrimeLocal
