-- Prove2me | solution 1 for WeierstrassEllipticZeta.sigma_regularized_coordinates_entire
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T22:21:39.632182+00:00
-- url     : https://prove2.me/submissions/5858a4d0-3da3-4a29-a3d7-bc2ed30533ad

import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.FinCases

noncomputable section
open Filter Set
open scoped Topology
open WeierstrassEllipticZeta

private lemma exp_six_bound (t : ℝ) (ht : 1 ≤ t) : (6 : ℝ) ≤ Real.exp (6 * t) := by
  have h := Real.add_one_le_exp (6 * t)
  linarith

private lemma entire_derivatives_quadratic_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2)))
    (z : ℂ) (n : ℕ) (hn : n ≤ 3) :
    ‖iteratedDeriv n f z‖ ≤ Real.exp ((3 * A + 6) * (1 + ‖z‖ ^ 2)) := by
  have ht : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have hcircle (w : ℂ) (hw : w ∈ Metric.sphere z 1) :
      ‖f w‖ ≤ Real.exp (3 * A * (1 + ‖z‖ ^ 2)) := by
    apply (hbound w).trans
    apply Real.exp_le_exp.mpr
    have hwz : ‖w‖ ≤ 1 + ‖z‖ := by
      have hdist := mem_sphere_iff_norm.mp hw
      calc ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
           _ = 1 + ‖z‖ := by rw [hdist]
    have hsq : ‖w‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg w) hwz 2
    have hrad : 1 + ‖w‖ ^ 2 ≤ 3 * (1 + ‖z‖ ^ 2) := by
      nlinarith [sq_nonneg (‖z‖ - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hrad hA]
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) hf.diffContOnCl hcircle
  have hfac : (n.factorial : ℝ) ≤ 6 := by
    interval_cases n <;> norm_num
  calc
    ‖iteratedDeriv n f z‖ ≤ n.factorial * Real.exp (3 * A * (1 + ‖z‖ ^ 2)) := by
      simpa using hc
    _ ≤ 6 * Real.exp (3 * A * (1 + ‖z‖ ^ 2)) := by gcongr
    _ ≤ Real.exp (6 * (1 + ‖z‖ ^ 2)) * Real.exp (3 * A * (1 + ‖z‖ ^ 2)) := by
      gcongr
      exact exp_six_bound _ ht
    _ = Real.exp ((3 * A + 6) * (1 + ‖z‖ ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring

private lemma sigma_second_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv D.sigma) z =
      (weierstrassZeta L z ^ 2 - L.weierstrassP z) * D.sigma z := by
  have heq : deriv D.sigma =ᶠ[𝓝 z] fun w ↦ weierstrassZeta L w * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (D.hasDerivAt w hw).deriv
  have h := ((hζ z hz).mul (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  ring

private lemma sigma_third_deriv (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (deriv (deriv D.sigma)) z =
      (weierstrassZeta L z ^ 3 - 3 * weierstrassZeta L z * L.weierstrassP z -
        L.derivWeierstrassP z) * D.sigma z := by
  have heq : deriv (deriv D.sigma) =ᶠ[𝓝 z]
      fun w ↦ (weierstrassZeta L w ^ 2 - L.weierstrassP w) * D.sigma w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact sigma_second_deriv L D hζ w hw
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  have h := ((((hζ z hz).pow 2).sub hp).mul
    (D.hasDerivAt z hz)).congr_of_eventuallyEq heq
  rw [h.deriv]
  simp only [Pi.sub_apply, Pi.pow_apply]
  ring

/-- The three pole-clearing factors have entire extensions with their normalized
values at the origin. No value of a totalized meromorphic function at a pole is used. -/
theorem solution (L : PeriodPair)
    (D : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z) :
    ∃ S : Fin 3 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (S j) univ) ∧
      (∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 3,
        S j z = D.sigma z ^ (j.val + 1) * ellipticPoleCoordinates L z j) ∧
      S 0 0 = 1 ∧ S 1 0 = 1 ∧ S 2 0 = -2 ∧
      ∀ A : ℝ, 0 ≤ A →
        (∀ z : ℂ, ‖D.sigma z‖ ≤ Real.exp (A * (1 + ‖z‖ ^ 2))) →
        ∀ (z : ℂ) (j : Fin 3),
          ‖S j z‖ ≤ Real.exp ((9 * A + 24) * (1 + ‖z‖ ^ 2)) := by
  let S : Fin 3 → ℂ → ℂ := ![
    deriv D.sigma,
    fun z ↦ deriv D.sigma z ^ 2 - D.sigma z * deriv (deriv D.sigma) z,
    fun z ↦ -2 * deriv D.sigma z ^ 3 +
      3 * D.sigma z * deriv D.sigma z * deriv (deriv D.sigma) z -
      D.sigma z ^ 2 * deriv (deriv (deriv D.sigma)) z]
  have hσ : AnalyticOnNhd ℂ D.sigma univ :=
    D.entire.differentiableOn.analyticOnNhd isOpen_univ
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j z _
    have h0 := hσ z trivial
    have h1 := h0.deriv
    have h2 := h1.deriv
    have h3 := h2.deriv
    fin_cases j
    · exact h1
    · exact (h1.pow 2).sub (h0.mul h2)
    · exact (((analyticAt_const.mul (h1.pow 3)).add
        (((analyticAt_const.mul h0).mul h1).mul h2))).sub ((h0.pow 2).mul h3)
  · intro z hz j
    have h1 := (D.hasDerivAt z hz).deriv
    have h2 := sigma_second_deriv L D h_zeta_deriv z hz
    have h3 := sigma_third_deriv L D h_zeta_deriv z hz
    fin_cases j <;> simp [S, ellipticPoleCoordinates, h1, h2, h3] <;> ring
  · simp [S, D.zero, D.deriv_zero.deriv]
  · simp [S, D.zero, D.deriv_zero.deriv]
  · simp [S, D.zero, D.deriv_zero.deriv]
  · intro A hA hbound z j
    let E := Real.exp ((3 * A + 6) * (1 + ‖z‖ ^ 2))
    have hE : 1 ≤ E := by
      apply Real.one_le_exp_iff.mpr
      positivity
    have hE0 : 0 ≤ E := le_trans (by norm_num) hE
    have hder (n : ℕ) (hn : n ≤ 3) : ‖iteratedDeriv n D.sigma z‖ ≤ E :=
      entire_derivatives_quadratic_bound D.sigma D.entire A hA hbound z n hn
    have h0 : ‖D.sigma z‖ ≤ E := by simpa using hder 0 (by omega)
    have h1 : ‖deriv D.sigma z‖ ≤ E := by simpa using hder 1 (by omega)
    have h2 : ‖deriv (deriv D.sigma) z‖ ≤ E := by
      simpa [iteratedDeriv_succ] using hder 2 (by omega)
    have h3 : ‖deriv (deriv (deriv D.sigma)) z‖ ≤ E := by
      simpa [iteratedDeriv_succ] using hder 3 (by omega)
    have hsmall : ‖S j z‖ ≤ 6 * E ^ 3 := by
      fin_cases j
      · have hE2 : 0 ≤ E * (E - 1) := mul_nonneg hE0 (sub_nonneg.mpr hE)
        have hE3 : 0 ≤ E ^ 2 * (E - 1) := mul_nonneg (sq_nonneg E) (sub_nonneg.mpr hE)
        exact h1.trans (by nlinarith)
      · change ‖deriv D.sigma z ^ 2 - D.sigma z * deriv (deriv D.sigma) z‖ ≤ _
        calc
          _ ≤ ‖deriv D.sigma z‖ ^ 2 + ‖D.sigma z‖ * ‖deriv (deriv D.sigma) z‖ := by
            have ht : ‖deriv D.sigma z ^ 2 - D.sigma z * deriv (deriv D.sigma) z‖ ≤
                ‖deriv D.sigma z ^ 2‖ + ‖D.sigma z * deriv (deriv D.sigma) z‖ :=
              norm_sub_le _ _
            rw [Complex.norm_pow, norm_mul] at ht
            exact ht
          _ ≤ E ^ 2 + E * E := by gcongr
          _ ≤ 6 * E ^ 3 := by nlinarith [mul_nonneg (sq_nonneg E) (sub_nonneg.mpr hE)]
      · change ‖-2 * deriv D.sigma z ^ 3 +
            3 * D.sigma z * deriv D.sigma z * deriv (deriv D.sigma) z -
            D.sigma z ^ 2 * deriv (deriv (deriv D.sigma)) z‖ ≤ _
        calc
          _ ≤ ‖-2 * deriv D.sigma z ^ 3‖ +
              ‖3 * D.sigma z * deriv D.sigma z * deriv (deriv D.sigma) z‖ +
              ‖D.sigma z ^ 2 * deriv (deriv (deriv D.sigma)) z‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ = 2 * ‖deriv D.sigma z‖ ^ 3 +
              3 * ‖D.sigma z‖ * ‖deriv D.sigma z‖ * ‖deriv (deriv D.sigma) z‖ +
              ‖D.sigma z‖ ^ 2 * ‖deriv (deriv (deriv D.sigma)) z‖ := by
            simp only [norm_mul, Complex.norm_pow]
            norm_num
          _ ≤ 2 * E ^ 3 + 3 * E * E * E + E ^ 2 * E := by gcongr
          _ = 6 * E ^ 3 := by ring
    apply hsmall.trans
    calc
      6 * E ^ 3 ≤ Real.exp (6 * (1 + ‖z‖ ^ 2)) * E ^ 3 := by
        gcongr
        exact exp_six_bound _ (by nlinarith [sq_nonneg ‖z‖])
      _ = Real.exp ((9 * A + 24) * (1 + ‖z‖ ^ 2)) := by
        dsimp only [E]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
