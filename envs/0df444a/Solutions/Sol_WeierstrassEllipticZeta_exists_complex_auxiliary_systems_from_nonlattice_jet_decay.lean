-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_nonlattice_jet_decay
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T00:38:22.699109+00:00
-- url     : https://prove2.me/submissions/eed4fb49-70e9-4896-8bfc-772002f787f8

import Theorems.Thm_WeierstrassEllipticZeta_nonlattice_common_denominator_bounds
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_arithmetic_jet_decay
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
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

noncomputable section
set_option maxHeartbeats 800000

/-- Absorb all arithmetic denominator factors into the nonlattice first-derivative bound. -/
private theorem nonlattice_arithmetic_first_derivative_decay
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_denominators : ∀ C : ℕ,
    ∃ B : ℝ, 0 < B ∧ ∀ (L : PeriodPair) (v z : ℂ) (N s : ℕ),
      1 ≤ Real.log N → ∀ P : NonlatticeCoordinatePresentation L θ ν v z C N s,
        let E : Fin 8 → ℂ := fun a =>
          MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
        let Q := E 1 * E 2 * E 3
        Q ≠ 0 ∧
          ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
              ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) ∧
          ∀ m l n : ℕ,
            ‖E 0 ^ m * (E 4 * E 5 * E 6 * E 7) ^ (m + 5 * l + n)‖ ≤
              Real.exp (B * ((m : ℝ) * Real.log N + m + 5 * l + n)))
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
                  Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728)) :
    ∀ (C : ℕ) (B K : ℝ), 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
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
                    Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456) := by
  intro C B K hB hK
  obtain ⟨A, hA, hden⟩ := h_denominators C
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (147456 * A * (7 + K))
  filter_upwards [h_parameters 1 zero_lt_one,
    h_nonlattice_decay (B + A) K (by positivity) hK, hlog,
    eventually_ge_atTop N₀] with N hpar hdec hlogN hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  rcases hpar with ⟨hm, hl, hs, hq, hsq, hdim, hlow, hupp, hml, hls, hrest⟩
  have hlm : l ≤ m := (Nat.le_mul_of_pos_right l (by positivity : 0 < s ^ 2)).trans hls
  have hmN : (m : ℝ) ≤ N := by
    have := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg m)
    dsimp [m] at *
    nlinarith only [this, hml]
  have hlm' : (l : ℝ) ≤ m := by exact_mod_cast hlm
  have hlN : (l : ℝ) ≤ N := hlm'.trans hmN
  dsimp only
  intro c hc hzero v hv hvl P n hn hbefore
  let E : Fin 8 → ℂ := fun a =>
    MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν] (P.denominator a)
  let Q : ℂ := E 1 * E 2 * E 3
  let W : ℂ := E 0 ^ m * (E 4 * E 5 * E 6 * E 7) ^ (m + 5 * l + n)
  obtain ⟨hQne, hQ, hW⟩ := hden L v (u₁ / 2) N s hlogN P
  have hT : 0 ≤ (s : ℝ) ^ 2 + Real.log N := by positivity
  have hc' : (∑ i, ‖c i‖) ≤ Real.exp ((B + A) * N) :=
    hc.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hA.le (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  have hQ' : ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
      ‖Q * L.derivWeierstrassP v‖ ≤ Real.exp ((B + A) * ((s : ℝ) ^ 2 + Real.log N)) :=
    hQ.trans (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hB hT]))
  have hsmall := hdec c hc' hzero v hv hvl Q hQ' n hn hbefore
  have hnN : (n : ℝ) ≤ K * N := hn.trans (mul_le_mul_of_nonneg_left hmN hK.le)
  have hW' : ‖W‖ ≤ Real.exp (A * (7 + K) * N) := by
    apply (hW m l n).trans
    apply Real.exp_le_exp.mpr
    have ht : (m : ℝ) * Real.log N + m + 5 * l + n ≤ (7 + K) * N := by
      nlinarith only [hml, hmN, hlN, hnN]
    exact (mul_le_mul_of_nonneg_left ht hA.le).trans_eq (by ring)
  have hsplit : (∏ a, E a ^ nonlatticeJetWeight m l n a) = W * Q ^ (5 * l) := by
    simp [Fin.prod_univ_succ, nonlatticeJetWeight, W, Q, mul_pow]
    ring
  rw [show (∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
      (P.denominator a) ^ nonlatticeJetWeight m l n a) = W * Q ^ (5 * l) from hsplit,
    mul_assoc W, mul_assoc W, norm_mul]
  calc
    _ ≤ Real.exp (A * (7 + K) * N) *
        Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) :=
      mul_le_mul hW' hsmall (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (A * (7 + K) * N - (N : ℝ) ^ 2 * Real.log N / 73728) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456) := by
      apply Real.exp_le_exp.mpr
      have ht : 147456 * A * (7 + K) ≤ (N : ℝ) :=
        hN₀.trans (by exact_mod_cast hN)
      have h1 := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N)
      have h2 := mul_le_mul_of_nonneg_left hlogN (sq_nonneg (N : ℝ))
      nlinarith only [h1, h2]

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
                  Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have hsmall := nonlattice_arithmetic_first_derivative_decay L ω u₁ u₂ θ ν
    h_parameters (nonlattice_common_denominator_bounds θ ν) h_nonlattice_decay
  exact exists_complex_auxiliary_systems_from_arithmetic_jet_decay L ω u₁ u₂
    h_grid h_parameters h_decay h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g
    hg_monic hg_degree hg_kernel h_jet_systems h_nonlattice_bounds h_interpolation
    h_regularization h_cleared_entire d hd h_period_jets h_period_bounds h_grid_matrices
    h_data D S h_factors_entire h_factors_eq A hA h_sigma_growth h_factor_growth
    h_sigma_nonzero h_sigma_inverse h_period_decay h_scaled_cleared_growth h_nonlattice_decay hsmall
