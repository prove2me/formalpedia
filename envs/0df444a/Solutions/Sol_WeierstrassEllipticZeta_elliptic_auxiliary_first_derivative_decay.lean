-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_auxiliary_first_derivative_decay
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T23:26:38.935813+00:00
-- url     : https://prove2.me/submissions/cdd89377-9290-4fe2-be89-aa682bc04f9f

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 800000
open Filter Metric Set
open scoped Topology

open WeierstrassEllipticZeta

private lemma auxiliary_radius_power_bound (N m : ℕ) (hN : (1 : ℝ) ≤ N)
    (hm : (m : ℝ) * Real.log N ≤ N) :
    auxiliaryRadius N ^ m ≤ Real.exp N := by
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  rw [auxiliaryRadius, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
    Real.rpow_def_of_pos hN0]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  nlinarith [mul_nonneg (Nat.cast_nonneg m) hlog]

/-- Sigma regularization makes the first possibly nonzero auxiliary jet small. -/
theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_decay : AuxiliaryGridDecayData ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (D : EllipticSigmaDifferentialData L) (S : Fin 3 → ℂ → ℂ)
    (h_factors_entire : ∀ j, AnalyticOnNhd ℂ (S j) univ)
    (h_factors_eq : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
      S j z = D.sigma z ^ (j.val + 1) * ellipticPoleCoordinates L z j)
    (A : ℝ) (hA : 0 < A)
    (h_sigma_growth : ∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_factor_growth : ∀ (z : ℂ) (j : Fin 3),
      ‖S j z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (h_sigma_nonzero : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0) :
    ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
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
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 73728) := by
  intro B K hB hK
  filter_upwards [h_parameters (6 * A) (by positivity),
    h_decay (B + 2) K (by positivity) hK, eventually_ge_atTop (1 : ℕ)] with N hpar hdec hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let R := auxiliaryRadius N
  let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N]
  let r := 4 * (auxiliaryS3 N : ℝ) * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
  rcases hpar with ⟨_, _, _, _, _, _, _, _, hmlog, _, hR, hr, _, _, hAG⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hR' : 1 ≤ R := hR
  have hR0 : 0 ≤ R := le_trans zero_le_one hR'
  have hRR : 1 ≤ R ^ 2 := by nlinarith
  have hRpow : R ^ m ≤ Real.exp N := auxiliary_radius_power_bound N m hN' hmlog
  dsimp only
  intro c hc
  let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
    L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
  let e : (Fin (m + 1) × Fin (l + 1) × Fin (l + 1)) → Fin 3 → ℕ :=
    fun i => ![i.2.2.val, i.2.1.val, 0]
  have he : ∀ i, e i 0 + 2 * e i 1 + 3 * e i 2 ≤ 3 * l := by
    intro i
    have h1 := i.2.1.isLt
    have h2 := i.2.2.isLt
    dsimp [e]
    omega
  obtain ⟨G, hG, hGeq, hGbound, _⟩ := h_regularization D.sigma S
    (fun z _ => D.entire.analyticAt z) h_factors_entire h_factors_eq
    0 c (fun i => i.1.val) e m (3 * l) (fun i => by have := i.1.isLt; omega) he
  have hsum : ellipticRegularizationSum L 0 c (fun i => i.1.val) e = f := by
    funext z
    dsimp [ellipticRegularizationSum, f, e, ellipticPoleCoordinates]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_zero, mul_one, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hGeq
  have hf (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ f z := by
    have hzeta : AnalyticAt ℂ (weierstrassZeta L) z :=
      (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
        fun w hw => (h_zeta_deriv w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
          L.isClosed_lattice.isOpen_compl z hz
    apply Finset.analyticAt_fun_sum
    intro i _
    exact
      ((analyticAt_const.mul (analyticAt_id.pow _)).mul
        ((L.analyticOnNhd_weierstrassP z hz).pow _)).mul (hzeta.pow _)
  have hψ (z : ℂ) : AnalyticAt ℂ (fun w => D.sigma w ^ (3 * l)) z :=
    (D.entire.analyticAt z).pow _
  have hlocal (z : ℂ) (hz : z ∉ L.lattice) :
      G =ᶠ[𝓝 z] fun w => D.sigma w ^ (3 * l) * f w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact hGeq w hw
  let H := Real.exp (A * (1 + R ^ 2))
  have hH : 1 ≤ H := Real.one_le_exp (by positivity)
  have hHbound (z : ℂ) (hz : ‖z‖ ≤ R) :
      ‖D.sigma z‖ ≤ H ∧ ∀ j, ‖S j z‖ ≤ H := by
    have hzz : ‖z‖ ^ 2 ≤ R ^ 2 := by nlinarith [mul_self_le_mul_self (norm_nonneg z) hz]
    have hh : Real.exp (A * (1 + ‖z‖ ^ 2)) ≤ H := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact ⟨(h_sigma_growth z).trans hh, fun j => (h_factor_growth z j).trans hh⟩
  have hHp : H ^ (3 * l) ≤ Real.exp ((N : ℝ) ^ 2) := by
    dsimp [H]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have h := mul_le_mul_of_nonneg_left hRR (show 0 ≤ 3 * A * (l : ℝ) by positivity)
    change 6 * A * (l : ℝ) * R ^ 2 ≤ (N : ℝ) ^ 2 at hAG
    nlinarith
  have houter : ∀ z ∈ sphere (0 : ℂ) R,
      ‖G z‖ ≤ Real.exp ((B + 2) * (N : ℝ) ^ 2) := by
    intro z hz
    have hz' : ‖z‖ ≤ R := by simpa only [mem_sphere, dist_zero_right] using (le_of_eq hz)
    have hg := hGbound R H hH hHbound z hz'
    simp only [norm_zero, add_zero, max_eq_right hR'] at hg
    calc
      _ ≤ (∑ i, ‖c i‖) * R ^ m * H ^ (3 * l) := hg
      _ ≤ Real.exp (B * N) * Real.exp N * Real.exp ((N : ℝ) ^ 2) := by
        apply mul_le_mul _ hHp (by positivity) (by positivity)
        exact mul_le_mul hc hRpow (by positivity) (Real.exp_pos _).le
      _ = Real.exp (B * N + N + (N : ℝ) ^ 2) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hNN hB]
  intro hzero w hw hwR hinv n hn hfirst
  have hzero_image : Γ.image (fun z => z - (0 : ℂ)) = Γ := by simp
  have hdec' := hdec 0 (by simpa using (le_of_lt hr)) f G (fun z => D.sigma z ^ (3 * l)) hG
    (fun x hx => hf x (h_grid.shifted_grid_regular _ x (by simpa [hzero_image] using hx)))
    (fun x _ => hψ x)
    (fun x hx => hlocal x (h_grid.shifted_grid_regular _ x (by simpa [hzero_image] using hx)))
    (by simpa [f] using hzero) houter w hwR n hn
  apply hdec'.2 (hf w hw) (hψ w) (hlocal w hw) hfirst
    (pow_ne_zero _ (h_sigma_nonzero w hw))
  apply hinv.trans (Real.exp_le_exp.mpr ?_)
  nlinarith [sq_nonneg (N : ℝ), mul_nonneg hB (sq_nonneg (N : ℝ))]
