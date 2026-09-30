-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_period_jet_decay
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T23:51:09.9381+00:00
-- url     : https://prove2.me/submissions/9a26622f-70ce-45b7-8849-ede05d5b4897

import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth_weighted
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_scaled_cleared_growth
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
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

open Set
noncomputable section
set_option maxHeartbeats 800000

open Filter Metric

private lemma weighted_auxiliary_radius_bound (N m : ℕ) (hN : (1 : ℝ) ≤ N)
    (hm : (m : ℝ) * Real.log N ≤ N) :
    auxiliaryRadius N ^ m ≤ Real.exp N := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  rw [auxiliaryRadius, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
    Real.rpow_def_of_pos hN0]
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg m) hlog]

private lemma nonnegative_power_exp_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ Real.exp ((n : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ hx
  linarith [Real.add_one_le_exp x]

/-- Common moving-coordinate denominators preserve an exponential quadratic envelope. -/
private theorem scaled_cleared_auxiliary_outer_bound
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (σ : ℂ → ℂ) (S : Fin 3 → ℂ → ℂ)
    (A : ℝ) (hA : 0 < A)
    (h_sigma_growth : ∀ z : ℂ, ‖σ z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_factor_growth : ∀ (z : ℂ) (j : Fin 3),
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_weighted : ∀ {ι : Type} [Fintype ι] (v : ℂ), v ∉ L.lattice → ∀
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (D M : ℕ)
    , (∀ i, l₀ i ≤ D) → (∀ i, l₂ i ≤ M) → (∀ i, l₃ i ≤ M) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G univ ∧
      (∀ z : ℂ, z ∉ L.lattice → z + v ∉ L.lattice →
        G z = σ z ^ (15 * M) * ∑ i, c i *
          clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) z) ∧
      ∀ R B : ℝ, 1 ≤ B →
        (∀ z : ℂ, ‖z‖ ≤ R → ‖σ z‖ ≤ B ∧ ∀ j, ‖S j z‖ ≤ B) →
        ∀ z : ℂ, ‖z‖ ≤ R →
          ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D *
            (36 : ℝ) ^ (3 * M) *
            (1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ +
              ‖L.derivWeierstrassP v‖) ^ (5 * M) * B ^ (15 * M)) :
    ∀ B : ℝ, 0 ≤ B → ∀ᶠ N : ℕ in Filter.atTop,
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
              G z = σ z ^ (15 * l) * (Q ^ (5 * l) *
                clearedAuxiliarySum L v c (fun i => i.1.val) (fun i => i.2.1.val)
                  (fun i => i.2.2.val) l z)) ∧
            ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2) := by
  intro B hB
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop _)
  filter_upwards [h_parameters (30 * A) (by positivity), hlog,
    eventually_ge_atTop (1 : ℕ)] with N hpar hlog hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let R := auxiliaryRadius N
  rcases hpar with ⟨_, _, hs, _, _, _, _, _, hmlog, hls, hR, _, _, _, hAG⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hmN : (m : ℝ) ≤ N := by
    change (m : ℝ) * Real.log N ≤ N at hmlog
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)]
  have hlm : l ≤ m := by
    change l * s ^ 2 ≤ m at hls
    change 2 ≤ s at hs
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    nlinarith
  have hlN : (l : ℝ) ≤ N := (Nat.cast_le.mpr hlm).trans hmN
  have hllog : (l : ℝ) * Real.log N ≤ N :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlm) (by linarith)).trans hmlog
  have hlsR : (l : ℝ) * (s : ℝ) ^ 2 ≤ m := by exact_mod_cast hls
  have hR1 : 1 ≤ R := hR
  have hRR : 1 ≤ R ^ 2 := by nlinarith
  have hRpow := weighted_auxiliary_radius_bound N m hN1 hmlog
  have htwo : (2 : ℝ) ^ m ≤ Real.exp (2 * N) := by
    apply (nonnegative_power_exp_bound 2 (by norm_num) m).trans
    apply Real.exp_le_exp.mpr
    nlinarith
  have hconst : (36 : ℝ) ^ (3 * l) ≤ Real.exp (108 * N) := by
    apply (nonnegative_power_exp_bound 36 (by norm_num) (3 * l)).trans
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  let H := Real.exp (A * (1 + R ^ 2))
  have hH : 1 ≤ H := Real.one_le_exp (by positivity)
  have hbasic (z : ℂ) (hz : ‖z‖ ≤ R) :
      ‖σ z‖ ≤ H ∧ ∀ j, ‖S j z‖ ≤ H := by
    have hzz : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg z]
    have hh : Real.exp (A * (1 + ‖z‖ ^ 2)) ≤ H := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact ⟨(h_sigma_growth z).trans hh, fun j => (h_factor_growth z j).trans hh⟩
  have hHp : H ^ (15 * l) ≤ Real.exp ((N : ℝ) ^ 2) := by
    dsimp [H]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    change 30 * A * (l : ℝ) * R ^ 2 ≤ (N : ℝ) ^ 2 at hAG
    nlinarith [mul_le_mul_of_nonneg_left hRR (show 0 ≤ 15 * A * (l : ℝ) by positivity)]
  dsimp only
  intro c hc v hvR hv Q hQ
  obtain ⟨G, hG, hGeq, hGbound⟩ := h_weighted v hv c (fun i => i.1.val)
    (fun i => i.2.1.val) (fun i => i.2.2.val) m l
    (fun i => by have := i.1.isLt; omega)
    (fun i => by have := i.2.1.isLt; omega)
    (fun i => by have := i.2.2.isLt; omega)
  let V := 1 + ‖weierstrassZeta L v‖ + ‖L.weierstrassP v‖ + ‖L.derivWeierstrassP v‖
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hQV : ‖Q‖ * V ≤ Real.exp (B * ((s : ℝ) ^ 2 + Real.log N)) := by
    calc
      _ = ‖Q‖ + ‖Q * weierstrassZeta L v‖ + ‖Q * L.weierstrassP v‖ +
          ‖Q * L.derivWeierstrassP v‖ := by simp only [norm_mul]; dsimp [V]; ring
      _ ≤ _ := hQ
  have hmoving : ‖Q‖ ^ (5 * l) * V ^ (5 * l) ≤ Real.exp (10 * B * N) := by
    rw [← mul_pow]
    apply (pow_le_pow_left₀ (mul_nonneg (norm_nonneg Q) hV) hQV (5 * l)).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have hsuml : (l : ℝ) * ((s : ℝ) ^ 2 + Real.log N) ≤ 2 * N := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsuml (show 0 ≤ 5 * B by positivity)]
  have hXpow : (max 1 (R + ‖v‖)) ^ m ≤ Real.exp (3 * N) := by
    have hX : max 1 (R + ‖v‖) ≤ 2 * R := max_le (by linarith) (by linarith)
    calc
      _ ≤ (2 * R) ^ m := pow_le_pow_left₀ (by positivity) hX m
      _ = (2 : ℝ) ^ m * R ^ m := mul_pow _ _ _
      _ ≤ Real.exp (2 * N) * Real.exp N :=
        mul_le_mul htwo hRpow (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨fun z => Q ^ (5 * l) * G z, ?_, ?_, ?_⟩
  · intro z _
    exact analyticAt_const.mul (hG z trivial)
  · intro z hz hzv
    dsimp only
    rw [hGeq z hz hzv]
    dsimp [clearedAuxiliarySum]
    ring
  · intro z hz
    have hg := hGbound R H hH hbasic z hz
    change ‖G z‖ ≤ (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ m *
      (36 : ℝ) ^ (3 * l) * V ^ (5 * l) * H ^ (15 * l) at hg
    calc
      _ = ‖Q‖ ^ (5 * l) * ‖G z‖ := by rw [norm_mul, norm_pow]
      _ ≤ ‖Q‖ ^ (5 * l) * ((∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ m *
          (36 : ℝ) ^ (3 * l) * V ^ (5 * l) * H ^ (15 * l)) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = (∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ m * (36 : ℝ) ^ (3 * l) *
          (‖Q‖ ^ (5 * l) * V ^ (5 * l)) * H ^ (15 * l) := by ring
      _ ≤ Real.exp (B * N) * Real.exp (3 * N) * Real.exp (108 * N) *
          Real.exp (10 * B * N) * Real.exp ((N : ℝ) ^ 2) := by gcongr
      _ = Real.exp ((11 * B + 111) * N + (N : ℝ) ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hNN (show 0 ≤ 11 * B + 111 by positivity)]

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
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have houter := scaled_cleared_auxiliary_outer_bound L ω u₁ u₂ h_parameters D.sigma S
    A hA h_sigma_growth h_factor_growth (by
      intro ι inst v hv c l₀ l₂ l₃ M₀ M h₀ h₂ h₃
      exact cleared_addition_entire_growth_weighted L h_zeta_addition h_wp_addition
        D.sigma S (fun z _ => D.entire.analyticAt z) h_factors_entire h_factors_eq
        v hv c l₀ l₂ l₃ M₀ M h₀ h₂ h₃)
  exact exists_complex_auxiliary_systems_from_scaled_cleared_growth L ω u₁ u₂
    h_grid h_parameters h_decay h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g
    hg_monic hg_degree hg_kernel h_jet_systems h_nonlattice_bounds h_interpolation
    h_regularization h_cleared_entire d hd h_period_jets h_period_bounds h_grid_matrices
    h_data D S h_factors_entire h_factors_eq A hA h_sigma_growth h_factor_growth
    h_sigma_nonzero h_sigma_inverse h_period_decay houter
