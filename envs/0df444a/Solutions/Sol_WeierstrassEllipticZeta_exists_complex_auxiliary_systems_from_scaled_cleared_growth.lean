-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_scaled_cleared_growth
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T00:12:55.71681+00:00
-- url     : https://prove2.me/submissions/d075361c-7d3e-4113-9d87-1149d2f7dc3c

import Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_first_derivative
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_nonlattice_jet_decay
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

open Metric Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 800000

private lemma translated_shifted_grid_regular
    (L : PeriodPair) (ω u₁ u₂ : ℂ) (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (A B : Fin 3 → ℕ) (x v : ℂ)
    (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) (hv : v ∈ auxiliaryGrid u₁ u₂ ω B) :
    x - v ∉ L.lattice := by
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨a, _, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨b, _, rfl⟩
  have heq : integerGridPoint u₁ u₂ ω (fun i => (a i : ℤ)) + u₁ / 2 -
      integerGridPoint u₁ u₂ ω (fun i => (b i : ℤ)) =
      integerGridPoint u₁ u₂ ω (fun i => (a i : ℤ) - (b i : ℤ)) + u₁ / 2 := by
    simp only [integerGridPoint, Int.cast_sub]
    ring
  rw [heq]
  exact h_grid.shifted_regular (fun i => (a i : ℤ) - (b i : ℤ))

private lemma enlarged_grid_radius_bound
    (L : PeriodPair) (ω u₁ u₂ : ℂ) (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (s q : ℕ) (hsq : s ≤ q) (hq : 1 ≤ q) (v : ℂ)
    (hv : v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]) :
    ‖v‖ ≤ 4 * (q : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1) := by
  have hv' : v + u₁ / 2 ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q] :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have hrad := h_grid.shifted_grid_radius _ _ hv'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_mul, Nat.cast_ofNat] at hrad
  have hnorm : ‖u₁ / 2‖ = ‖u₁‖ / 2 := by norm_num [norm_div]
  have htriangle := norm_sub_le (v + u₁ / 2) (u₁ / 2)
  rw [add_sub_cancel_right, hnorm] at htriangle
  have hsqr : (s : ℝ) ≤ q := by exact_mod_cast hsq
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 := mul_le_mul_of_nonneg_right hsqr (norm_nonneg u₁)
  have h2 := mul_le_mul_of_nonneg_right hsqr (norm_nonneg u₂)
  have h3 := mul_le_mul_of_nonneg_right hqr (norm_nonneg u₁)
  nlinarith only [hrad, htriangle, h1, h2, h3, hqr,
    mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₁),
    mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₂),
    mul_nonneg (Nat.cast_nonneg q) (norm_nonneg ω)]

/-- Nonlattice interpolation recovers the exact cleared first derivative at the fixed base point. -/
private theorem scaled_nonlattice_first_derivative_decay
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_decay : AuxiliaryGridDecayData ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L)
    (h_sigma_nonzero : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (h_sigma_inverse : ∀ᶠ N : ℕ in Filter.atTop,
      ‖D.sigma (u₁ / 2) ^ (15 * auxiliaryL N)‖⁻¹ ≤ Real.exp ((N : ℝ) ^ 2))
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
    (h_first : ∀ {ι : Type} [Fintype ι] (v : ℂ), v ∉ L.lattice → ∀
    (c : ι → ℂ) (l₀ l₂ l₃ : ι → ℕ) (M : ℕ)
    (z : ℂ), z ∉ L.lattice → z + v ∉ L.lattice →
    AnalyticAt ℂ (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z ∧
      ∀ n : ℕ,
        (∀ j < n, iteratedDeriv j (fun w => ∑ i, c i * w ^ l₀ i *
          L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v) = 0) →
        iteratedDeriv n (clearedAuxiliarySum L v c l₀ l₂ l₃ M) z =
          (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) *
            iteratedDeriv n (fun w => ∑ i, c i * w ^ l₀ i *
              L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i) (z + v)) :
    ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
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
                  Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) := by
  intro B K hB hK
  filter_upwards [h_parameters 1 zero_lt_one, h_sigma_inverse,
    h_scaled_cleared_growth B hB, h_decay (11 * B + 112) K (by positivity) hK,
    eventually_ge_atTop (1 : ℕ)] with N hpar hinv hgrowth hdec hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let q := auxiliaryS3 N
  let R := auxiliaryRadius N
  let r := 4 * (q : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
  let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, q]
  rcases hpar with ⟨_, _, _, hq, hsq, _, _, _, _, _, hR, hr, _, hratio, _⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hratio' : 2 * r / R ≤ 1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num))
  have h2r : 2 * r ≤ R := (div_le_one hRpos).mp hratio'
  have hbase : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  have hbaseR : ‖u₁ / 2‖ + 1 ≤ 2 * r := by
    have hnorm : ‖u₁ / 2‖ = ‖u₁‖ / 2 := by norm_num [norm_div]
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqu := mul_le_mul_of_nonneg_right hqr (norm_nonneg u₁)
    rw [hnorm]
    dsimp only [r]
    nlinarith only [hqr, hqu,
      mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₁),
      mul_nonneg (Nat.cast_nonneg q) (norm_nonneg u₂),
      mul_nonneg (Nat.cast_nonneg q) (norm_nonneg ω)]
  dsimp only
  intro c hc
  let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
    L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
  intro hzero v hv hvL Q hQ n hn hbefore
  have hvr : ‖v‖ ≤ r := enlarged_grid_radius_bound L ω u₁ u₂ h_grid s q hsq hq v hv
  have hvR : ‖v‖ ≤ R := hvr.trans (by linarith)
  obtain ⟨G, hG, hGeq, hGbound⟩ := hgrowth c hc v hvR hvL Q hQ
  let f : ℂ → ℂ := fun z => Q ^ (5 * l) *
    clearedAuxiliarySum L v c (fun i => i.1.val) (fun i => i.2.1.val)
      (fun i => i.2.2.val) l z
  have hf (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) : AnalyticAt ℂ f z :=
    analyticAt_const.mul (h_first v hvL c (fun i => i.1.val) (fun i => i.2.1.val)
      (fun i => i.2.2.val) l z hz hp).1
  have hjet (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) (j : ℕ)
      (hbefore : ∀ k < j, iteratedDeriv k F (z + v) = 0) :
      iteratedDeriv j f z = Q ^ (5 * l) *
        (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * l) * iteratedDeriv j F (z + v) := by
    dsimp only [f]
    rw [iteratedDeriv_const_mul_field,
      (h_first v hvL c (fun i => i.1.val) (fun i => i.2.1.val)
        (fun i => i.2.2.val) l z hz hp).2 j hbefore]
    ring
  have hlocal (z : ℂ) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice) :
      G =ᶠ[𝓝 z] fun w => D.sigma w ^ (15 * l) * f w := by
    have hnear := (continuousAt_id.add_const v).eventually
      (L.isClosed_lattice.isOpen_compl.mem_nhds hp)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz, hnear] with w hw hwp
    exact hGeq w hw hwp
  have hnodes (x : ℂ) (hx : x ∈ Γ.image (fun z => z - v)) :
      x ∉ L.lattice ∧ x + v ∉ L.lattice := by
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact ⟨translated_shifted_grid_regular L ω u₁ u₂ h_grid _ _ y v hy hv,
      by simpa using h_grid.shifted_grid_regular _ y hy⟩
  have hfj : ∀ x ∈ Γ.image (fun z => z - v), ∀ j < m + 1, iteratedDeriv j f x = 0 := by
    intro x hx j hj
    obtain ⟨hxL, hxp⟩ := hnodes x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rw [hjet (y - v) hxL hxp j (by
      intro k hk
      simpa using hzero y hy k (hk.trans hj))]
    simp only [sub_add_cancel]
    rw [hzero y hy j hj, mul_zero]
  have hbasep : u₁ / 2 + v ∉ L.lattice := by
    apply h_grid.shifted_grid_regular ![3 * s, 3 * s, 3 * q]
    exact Finset.mem_image.mpr ⟨v, hv, add_comm _ _⟩
  have hbeforef : ∀ j < n, iteratedDeriv j f (u₁ / 2) = 0 := by
    intro j hj
    rw [hjet _ hbase hbasep j (fun k hk => hbefore k (hk.trans hj)), hbefore j hj, mul_zero]
  have houter : ∀ z ∈ sphere (0 : ℂ) R, ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2) := by
    intro z hz
    exact hGbound z (by simpa only [mem_sphere, dist_zero_right] using le_of_eq hz)
  have hdec' := hdec v hvr f G (fun z => D.sigma z ^ (15 * l)) hG
    (fun x hx => hf x (hnodes x hx).1 (hnodes x hx).2)
    (fun x _ => (D.entire.analyticAt x).pow _)
    (fun x hx => hlocal x (hnodes x hx).1 (hnodes x hx).2)
    hfj houter (u₁ / 2) hbaseR n hn
  have hinv' : ‖D.sigma (u₁ / 2) ^ (15 * l)‖⁻¹ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2) := by
    apply hinv.trans (Real.exp_le_exp.mpr ?_)
    nlinarith [sq_nonneg (N : ℝ), mul_nonneg hB (sq_nonneg (N : ℝ))]
  have hsmall := hdec'.2 (hf _ hbase hbasep) ((D.entire.analyticAt _).pow _)
    (hlocal _ hbase hbasep) hbeforef (pow_ne_zero _ (h_sigma_nonzero _ hbase)) hinv'
  rwa [hjet _ hbase hbasep n hbefore] at hsmall

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
            ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ Real.exp ((11 * B + 112) * (N : ℝ) ^ 2)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have hsmall := scaled_nonlattice_first_derivative_decay L ω u₁ u₂ h_grid h_parameters
    h_decay D h_sigma_nonzero (h_sigma_inverse.mono fun N h => h.1)
    h_scaled_cleared_growth (by
      intro ι inst v hv c l₀ l₂ l₃ M z hz hp
      exact cleared_auxiliary_first_derivative L h_zeta_deriv v hv c l₀ l₂ l₃ M z hz hp)
  exact exists_complex_auxiliary_systems_from_nonlattice_jet_decay L ω u₁ u₂
    h_grid h_parameters h_decay h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g
    hg_monic hg_degree hg_kernel h_jet_systems h_nonlattice_bounds h_interpolation
    h_regularization h_cleared_entire d hd h_period_jets h_period_bounds h_grid_matrices
    h_data D S h_factors_entire h_factors_eq A hA h_sigma_growth h_factor_growth
    h_sigma_nonzero h_sigma_inverse h_period_decay h_scaled_cleared_growth hsmall
