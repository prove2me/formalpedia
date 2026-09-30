-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_bounded_auxiliary_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T00:18:24.274711+00:00
-- url     : https://prove2.me/submissions/db133351-56b6-4e83-a727-e8b1784d87b8

import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_jet_matrices_of_arithmetic_model
import Theorems.Thm_WeierstrassEllipticZeta_bounded_auxiliary_polynomial_of_grid_matrices

open scoped Polynomial
open Filter WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∃ p : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℤ[X][X],
        (fun i => (p i).eval₂ (Polynomial.aeval θ).toRingHom ν) ≠ 0 ∧
        (∀ i, (p i).natDegree < g.natDegree) ∧
        (∀ i j, (((p i).coeff j).natDegree : ℝ) ≤ C * m) ∧
        (∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ Real.exp (C * N)) ∧
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ n ≤ m, iteratedDeriv n (fun w => ∑ i,
            (p i).eval₂ (Polynomial.aeval θ).toRingHom ν * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) = 0  := by
  have hmat := auxiliary_grid_jet_matrices_of_arithmetic_model
    L ω u₁ u₂ h_grid θ hθ ν g hg_monic hg_degree hg_kernel d hd h_data
  exact bounded_auxiliary_polynomial_of_grid_matrices
    L ω u₁ u₂ θ ν g d hg_degree hg_kernel hmat
