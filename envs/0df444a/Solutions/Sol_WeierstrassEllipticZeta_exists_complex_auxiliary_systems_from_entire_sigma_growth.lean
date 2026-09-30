-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_entire_sigma_growth
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T23:00:54.773054+00:00
-- url     : https://prove2.me/submissions/1bc2f690-3681-489c-a9a2-ab3865f64271

import Theorems.Thm_WeierstrassEllipticZeta_sigma_period_inverse_bounds
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_sigma_inverse_bounds
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

private lemma period_coefficient_of_grid (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) (A : Fin 3 → ℕ)
    (v : ℂ) (hv : v ∈ auxiliaryGrid u₁ u₂ ω A) (hvL : v ∈ L.lattice) :
    ∃ a : ℤ, a.natAbs ≤ A 2 ∧ v = a * ω := by
  classical
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  let m : Fin 3 → ℤ := fun i => (t i : ℕ)
  have hm := (h_grid.lattice_iff m).mp hvL
  refine ⟨m 2, ?_, ?_⟩
  · simp [m, Nat.le_of_lt (t 2).isLt]
  · change integerGridPoint u₁ u₂ ω m = _
    simp [integerGridPoint, hm.1, hm.2]

/-- The two actual sigma regularizers have uniformly controlled reciprocal norms. -/
private theorem sigma_auxiliary_regularizer_inverse_bounds_from_progressions
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (hinv : ∀ u ω : ℂ, u ∉ L.lattice → ω ∈ L.lattice →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (k : ℕ),
        ‖D.sigma (u + n * ω) ^ k‖⁻¹ ≤
          Real.exp (C * k * (1 + (n : ℝ) ^ 2))) :
    (∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0) ∧
      ∀ᶠ N : ℕ in atTop,
        ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2) ∧
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω
            ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          v ∈ L.lattice →
            ‖D.sigma (u₁ / 2 + v) ^ (3 * auxiliaryL N)‖⁻¹ ≤
              Real.exp ((N : ℝ) ^ 2) := by
  refine ⟨hne, ?_⟩
  have hu : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  have hω : ω ∈ L.lattice := by
    simpa [integerGridPoint] using (h_grid.lattice_iff ![0, 0, 1]).mpr (by simp)
  obtain ⟨C, hC, hbound⟩ := hinv (u₁ / 2) ω hu hω
  filter_upwards [h_parameters (30 * C) (by positivity), eventually_ge_atTop (1 : ℕ)] with N hpar hN
  let l := auxiliaryL N
  let q := auxiliaryS3 N
  let R := auxiliaryRadius N
  let U := ‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1
  let r := 4 * (q : ℝ) * U
  rcases hpar with ⟨_, _, _, _, _, _, _, _, _, _, hR, _, _, hratio, hgrowth⟩
  have hR' : 1 ≤ R := hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR'
  have hU : 1 ≤ U := by
    dsimp [U]
    nlinarith [norm_nonneg u₁, norm_nonneg u₂, norm_nonneg ω]
  have hratio' : 2 * r / R ≤ 1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num))
  have h2r : 2 * r ≤ R := (div_le_one hRpos).mp hratio'
  have hqR : (q : ℝ) ≤ R := by
    have h := mul_le_mul_of_nonneg_left hU (show 0 ≤ (q : ℝ) by positivity)
    dsimp only [r] at h2r
    nlinarith [show 0 ≤ (q : ℝ) by positivity]
  have hRR : 1 ≤ R ^ 2 := by nlinarith
  have hgrowth' : 30 * C * (l : ℝ) * R ^ 2 ≤ (N : ℝ) ^ 2 := hgrowth
  constructor
  · have h := hbound 0 (15 * l)
    simp only [Int.cast_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0),
      Nat.cast_mul, Nat.cast_ofNat, mul_one] at h
    apply h.trans (Real.exp_le_exp.mpr ?_)
    have hm := mul_le_mul_of_nonneg_left hRR
      (show 0 ≤ 15 * C * (l : ℝ) by positivity)
    nlinarith [show 0 ≤ C * (l : ℝ) * R ^ 2 by positivity]
  · intro v hv hvL
    obtain ⟨a, ha, rfl⟩ := period_coefficient_of_grid L ω u₁ u₂ h_grid _ v hv hvL
    have ha' : (a.natAbs : ℝ) ≤ 3 * q := by
      change a.natAbs ≤ 3 * auxiliaryS3 N at ha
      exact_mod_cast ha
    have habs : |(a : ℝ)| ≤ 3 * R := by
      have hh : (a.natAbs : ℝ) ≤ 3 * R := ha'.trans (by linarith)
      simpa using hh
    have hasq : (a : ℝ) ^ 2 ≤ 9 * R ^ 2 := by
      have hh := mul_self_le_mul_self (abs_nonneg (a : ℝ)) habs
      nlinarith [sq_abs (a : ℝ)]
    have hb : 1 + (a : ℝ) ^ 2 ≤ 10 * R ^ 2 := by nlinarith
    apply (hbound a (3 * l)).trans (Real.exp_le_exp.mpr ?_)
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 * C * (l : ℝ) by positivity)
    push_cast
    nlinarith

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
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2))) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  obtain ⟨hne, hinv⟩ := sigma_period_inverse_bounds L D h_zeta_deriv
  obtain ⟨_, hscaled⟩ := sigma_auxiliary_regularizer_inverse_bounds_from_progressions
    L ω u₁ u₂ h_grid h_parameters D hne hinv
  exact exists_complex_auxiliary_systems_from_sigma_inverse_bounds L ω u₁ u₂
    h_grid h_parameters h_decay h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g
    hg_monic hg_degree hg_kernel h_jet_systems h_nonlattice_bounds h_interpolation
    h_regularization h_cleared_entire d hd h_period_jets h_period_bounds h_grid_matrices
    h_data D S h_factors_entire h_factors_eq A hA h_sigma_growth h_factor_growth hne hscaled
