-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_sigma_inverse_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T23:24:31.533871+00:00
-- url     : https://prove2.me/submissions/e508ee06-48a0-49a2-8490-5ed583864e75

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_auxiliary_first_derivative_decay
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_period_jet_decay
import Mathlib.Tactic.LinearCombination
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

/-- The period denominator is absorbed while retaining quadratic logarithmic decay. -/
private theorem period_auxiliary_arithmetic_decay_from_first_derivative
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) (δ : ℂ)
    (h_sigma_inverse : ∀ᶠ N : ℕ in Filter.atTop,
      ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) ∧
      ∀ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
        v ∈ L.lattice →
          ‖D.sigma (u₁ / 2 + v) ^ (3 * auxiliaryL N)‖⁻¹ ≤
            Real.exp ((N : ℝ) ^ 2))
    (h_first : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let r := 4 * (auxiliaryS3 N : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ w : ℂ, w ∉ L.lattice → ‖w‖ + 1 ≤ 2 * r →
          ‖D.sigma w ^ (3 * l)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) →
          ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f w = 0) →
            ‖iteratedDeriv n f w‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728)) :
    ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
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
            ‖δ ^ (7 * (m + 2 * l + n)) * iteratedDeriv n f (u₁ / 2 + v)‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456) := by
  intro B K hB hK
  let C := 7 * (‖δ‖ + 1) * (K + 3)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog : ∀ᶠ N : ℕ in atTop, max 1 (147456 * C) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop _)
  filter_upwards [h_parameters 1 zero_lt_one, h_sigma_inverse,
    h_first (B + 3) K (by positivity) hK, hlog, eventually_ge_atTop (1 : ℕ)]
    with N hpar hinv hfirst hlog hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  rcases hpar with ⟨_, _, hs, _, _, _, _, _, hmlog, hls, _, hr, hgeom, _, _⟩
  have hlog1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hlogC : 147456 * C ≤ Real.log N := (le_max_right _ _).trans hlog
  have hmN : (m : ℝ) ≤ N := by
    change (m : ℝ) * Real.log N ≤ N at hmlog
    nlinarith [mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg m)]
  have hlm : l ≤ m := by
    change l * auxiliaryS N ^ 2 ≤ m at hls
    have hs2 : 1 ≤ auxiliaryS N ^ 2 := by nlinarith
    nlinarith
  have hlN : (l : ℝ) ≤ N := (Nat.cast_le.mpr hlm).trans hmN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hmexp : (m : ℝ) + 1 ≤ Real.exp N := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hlexp : (l : ℝ) + 1 ≤ Real.exp N := by
    linarith [Real.add_one_le_exp (N : ℝ)]
  dsimp only
  intro c hc
  let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
    L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
  have hcard : ((m + 1 : ℝ) * (l + 1) * (l + 1)) ≤ Real.exp (3 * N) := by
    calc
      _ ≤ Real.exp N * Real.exp N * Real.exp N := by
        exact mul_le_mul (mul_le_mul hmexp hlexp (by positivity) (by positivity))
          hlexp (by positivity) (by positivity)
      _ = _ := by rw [show 3 * (N : ℝ) = N + N + N by ring, Real.exp_add, Real.exp_add]
  have hsum : (∑ i, ‖c i‖) ≤ Real.exp ((B + 3) * N) := by
    calc
      _ ≤ ∑ _i : Fin (m + 1) × Fin (l + 1) × Fin (l + 1), Real.exp (B * N) :=
        Finset.sum_le_sum (fun i _ => hc i)
      _ = ((m + 1 : ℝ) * (l + 1) * (l + 1)) * Real.exp (B * N) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ Real.exp (3 * N) * Real.exp (B * N) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by rw [show (B + 3) * (N : ℝ) = 3 * N + B * N by ring, Real.exp_add]
  intro hzero v hv hvL n hn hbefore
  have hv' : u₁ / 2 + v ∈ shiftedAuxiliaryGrid u₁ u₂ ω
      ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N] := by
    exact Finset.mem_image.mpr ⟨v, hv, add_comm _ _⟩
  obtain ⟨hwL, hwR⟩ := hgeom _ hv'
  have hsmall := hfirst c hsum hzero (u₁ / 2 + v) hwL
    (by linarith) (hinv.2 v hv hvL) n hn hbefore
  have hpower : ‖δ ^ (7 * (m + 2 * l + n))‖ ≤ Real.exp (C * (N : ℝ) ^ 2) := by
    rw [norm_pow]
    have hdexp : ‖δ‖ ≤ Real.exp ‖δ‖ := by linarith [Real.add_one_le_exp ‖δ‖]
    calc
      _ ≤ (Real.exp ‖δ‖) ^ (7 * (m + 2 * l + n)) :=
        pow_le_pow_left₀ (norm_nonneg δ) hdexp _
      _ = Real.exp ((7 * (m + 2 * l + n) : ℕ) * ‖δ‖) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hnN : (n : ℝ) ≤ K * N := hn.trans (mul_le_mul_of_nonneg_left hmN hK.le)
        have hp : (7 * (m + 2 * l + n) : ℝ) ≤ 7 * (3 + K) * N := by
          nlinarith
        push_cast
        calc
          _ ≤ (7 * (3 + K) * N) * ‖δ‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg δ)
          _ ≤ C * N := by dsimp [C]; nlinarith [norm_nonneg δ]
          _ ≤ _ := mul_le_mul_of_nonneg_left hNN hC
  calc
    _ = ‖δ ^ (7 * (m + 2 * l + n))‖ * ‖iteratedDeriv n f (u₁ / 2 + v)‖ := norm_mul _ _
    _ ≤ Real.exp (C * (N : ℝ) ^ 2) *
        Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) :=
      mul_le_mul hpower hsmall (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (C * (N : ℝ) ^ 2 - (N : ℝ) ^ 2 * Real.log N / 73728) := by
      rw [sub_eq_add_neg, Real.exp_add]
      congr 2
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hlogC (sq_nonneg (N : ℝ))]

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
            Real.exp ((N : ℝ) ^ 2)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have hfirst := elliptic_auxiliary_first_derivative_decay L ω u₁ u₂ h_grid h_parameters
    h_decay h_zeta_deriv h_regularization D S h_factors_entire h_factors_eq A hA
    h_sigma_growth h_factor_growth h_sigma_nonzero
  have hperiod := period_auxiliary_arithmetic_decay_from_first_derivative
    L ω u₁ u₂ h_parameters D (Polynomial.aeval θ d) h_sigma_inverse hfirst
  exact exists_complex_auxiliary_systems_from_period_jet_decay L ω u₁ u₂
    h_grid h_parameters h_decay h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g
    hg_monic hg_degree hg_kernel h_jet_systems h_nonlattice_bounds h_interpolation
    h_regularization h_cleared_entire d hd h_period_jets h_period_bounds h_grid_matrices
    h_data D S h_factors_entire h_factors_eq A hA h_sigma_growth h_factor_growth
    h_sigma_nonzero h_sigma_inverse hperiod
