-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_arithmetic_jet_decay
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T01:14:00.16333+00:00
-- url     : https://prove2.me/submissions/4a5481fa-0a08-439f-98bf-6ad5b1008f20

import Theorems.Thm_WeierstrassEllipticZeta_complex_auxiliary_systems_of_bounded_grid_derivatives
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_grid_bounded_nonzero_derivative
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_WeierstrassEllipticZeta_NonlatticeJetBounds
import Definitions.Def_WeierstrassEllipticZeta_PeriodJetBounds
import Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
import Definitions.Def_WeierstrassEllipticZeta_ReducedJetSystems
import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Definitions.Def_WeierstrassEllipticZeta_PeriodJets
import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

open scoped Polynomial
open Filter

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_decay : AuxiliaryGridDecayData ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g)
    (h_nonlattice_bounds : BoundedAuxiliaryNonlatticeJetData L θ ν g)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂)
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (h_cleared_entire : ClearedAdditionEntireData L ω u₁ u₂)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_period_jets : PeriodArithmeticJetSystemData L ω (u₁ / 2) θ ν g d)
    (h_period_bounds : BoundedAuxiliaryPeriodJetData L ω (u₁ / 2) θ ν g d)
    (h_grid_matrices : AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i))
    (D : EllipticSigmaDifferentialData L) (S : Fin 3 → ℂ → ℂ)
    (h_factors_entire : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (h_factors_eq : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = D.sigma z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (h_sigma_growth : ∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_factor_growth : ∀ (z : ℂ) (j : Fin 3),
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_sigma_nonzero : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (h_sigma_inverse : ∀ᶠ N : ℕ in Filter.atTop,
      ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) ∧
      ∀ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
        v ∈ L.lattice →
          ‖D.sigma (u₁ / 2 + v) ^ (3 * auxiliaryL N)‖⁻¹ ≤
            Real.exp ((N : ℝ) ^ 2))
    (h_period_decay : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∀ i, ‖c i‖ ≤ Real.exp (B * N)) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω
            ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          v ∈ L.lattice → ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f (u₁ / 2 + v) = 0) →
            ‖(Polynomial.aeval θ d) ^ (7 * (m + 2 * l + n)) * iteratedDeriv n f (u₁ / 2 + v)‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456))
    (h_scaled_cleared_growth : ∀ B : ℝ, 0 ≤ B → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      let R := auxiliaryRadius N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        ∀ v : ℂ, ‖v‖ ≤ R → v ∉ L.lattice → ∀ Q : ℂ,
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) →
          ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G Set.univ ∧
            (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
              G z = D.sigma z ^ (15 * l) * (Q ^ (5 * l) *
                clearedAuxiliarySum L v c (fun i => i.1.val) (fun i => i.2.1.val)
                  (fun i => i.2.2.val) l z)) ∧
            ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2))
    (h_nonlattice_decay : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice → ∀ Q : ℂ,
            ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) →
            ∀ n : ℕ, (n : ℝ) ≤ K * m →
              (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
              ‖Q ^ (5 * l) * (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^
                (3 * l) * iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                  Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728))
    (h_arithmetic_nonlattice_decay : ∀ (C : ℕ) (B K : ℝ), 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice →
            ∀ P : NonlatticeCoordinatePresentation L θ ν v (u₁ / 2) C N s,
              ∀ n : ℕ, (n : ℝ) ≤ K * m →
                (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
                ‖(∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
                    (P.denominator a) ^ nonlatticeJetWeight m l n a) *
                  (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^ (3 * l) *
                  iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                    Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  exact complex_auxiliary_systems_of_bounded_grid_derivatives L ω u₁ u₂ θ ν g d
    hg_degree hd h_grid h_parameters h_zeta_deriv h_zeta_addition h_grid_matrices
    h_period_decay h_arithmetic_nonlattice_decay
    (auxiliary_grid_bounded_nonzero_derivative L ω u₁ u₂ h_grid)
