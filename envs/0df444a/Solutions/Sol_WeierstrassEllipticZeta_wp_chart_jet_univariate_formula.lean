-- Prove2me | solution 1 for WeierstrassEllipticZeta.wp_chart_jet_univariate_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T03:47:49.594409+00:00
-- url     : https://prove2.me/submissions/438149d9-6488-434e-996b-72e14d130800

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.ComputeDegree

noncomputable section
open WeierstrassEllipticZeta Polynomial
open scoped Classical Topology

private def wpJetStep (g₂ g₃ : ℂ) (p : Polynomial ℂ) : Polynomial ℂ :=
  (C 4 * X ^ 3 - C g₂ * X - C g₃) * p.derivative.derivative +
    (C 6 * X ^ 2 - C (g₂ / 2)) * p.derivative

private lemma wpJetStep_degree (g₂ g₃ : ℂ) (p : Polynomial ℂ) :
    (wpJetStep g₂ g₃ p).natDegree ≤ p.natDegree + 1 := by
  have hb : (C 4 * X ^ 3 - C g₂ * X - C g₃).natDegree ≤ 3 := by compute_degree
  have ha : (C 6 * X ^ 2 - C (g₂ / 2)).natDegree ≤ 2 := by compute_degree
  apply natDegree_add_le_of_degree_le
  · by_cases hpp : p.derivative.derivative = 0
    · simp [hpp]
    have hp' : p.derivative.natDegree ≠ 0 := by
      intro h
      exact hpp (derivative_of_natDegree_zero h)
    have hp : p.natDegree ≠ 0 := by
      intro h
      have hzero := derivative_of_natDegree_zero h
      simp [hzero] at hp'
    have hd := natDegree_derivative_lt hp
    have hd' := natDegree_derivative_lt hp'
    exact natDegree_mul_le.trans (show _ ≤ p.natDegree + 1 by omega)
  · by_cases hp' : p.derivative = 0
    · simp [hp']
    have hp : p.natDegree ≠ 0 := by
      intro h
      exact hp' (derivative_of_natDegree_zero h)
    have hd := natDegree_derivative_lt hp
    exact natDegree_mul_le.trans (show _ ≤ p.natDegree + 1 by omega)

private lemma wpJetStep_iterate_degree (g₂ g₃ : ℂ) (p : Polynomial ℂ) (r : ℕ) :
    ((wpJetStep g₂ g₃)^[r] p).natDegree ≤ p.natDegree + r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (wpJetStep_degree _ _ _).trans (by omega)

private lemma sigma_ne_zero (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    G.D.sigma z ≠ 0 := by
  intro hzero
  obtain ⟨j, hj⟩ := G.hS_ne z
  rw [G.hS_value z hz j, hzero, zero_pow (by decide), zero_mul] at hj
  exact hj rfl

private lemma chart_regular_values (G : Frontier.Geometry) (z : ℂ)
    (hz : z ∉ G.L.lattice) :
    G.S 0 z ≠ 0 ∧ G.S 1 z / G.S 0 z = G.L.weierstrassP z ∧
      G.S 2 z / G.S 0 z = G.L.derivWeierstrassP z := by
  simp [G.hS_value z hz, sigma_ne_zero G z hz]

private lemma wp_flow (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    HasDerivAt G.L.weierstrassP (G.L.derivWeierstrassP z) z ∧
      HasDerivAt G.L.derivWeierstrassP (6 * G.L.weierstrassP z ^ 2 - G.L.g₂ / 2) z := by
  obtain ⟨hzero, hx, hy⟩ := chart_regular_values G z hz
  have hflow := G.hflow.1 z hzero
  rw [hx, hy] at hflow
  have hnear := G.L.isClosed_lattice.isOpen_compl.mem_nhds hz
  refine ⟨hflow.1.congr_of_eventuallyEq ?_, hflow.2.1.congr_of_eventuallyEq ?_⟩
  · filter_upwards [hnear] with w hw
    exact (chart_regular_values G w hw).2.1.symm
  · filter_upwards [hnear] with w hw
    exact (chart_regular_values G w hw).2.2.symm

private lemma deriv_wp_polynomial (G : Frontier.Geometry) (p : Polynomial ℂ)
    (z : ℂ) (hz : z ∉ G.L.lattice) :
    deriv (fun w => p.eval (G.L.weierstrassP w)) z =
      G.L.derivWeierstrassP z * p.derivative.eval (G.L.weierstrassP z) := by
  simpa [Function.comp_def, mul_comm] using
    ((p.hasDerivAt _).comp z (wp_flow G z hz).1).deriv

private lemma deriv_wp_weighted_polynomial (G : Frontier.Geometry) (p : Polynomial ℂ)
    (z : ℂ) (hz : z ∉ G.L.lattice) :
    deriv (fun w => G.L.derivWeierstrassP w * p.derivative.eval (G.L.weierstrassP w)) z =
      (wpJetStep G.L.g₂ G.L.g₃ p).eval (G.L.weierstrassP z) := by
  have hf := wp_flow G z hz
  have hd := (hf.2.mul ((p.derivative.hasDerivAt _).comp z hf.1)).deriv
  simp only [Pi.mul_def, Function.comp_def] at hd
  rw [hd]
  simp only [wpJetStep, eval_add, eval_mul, eval_sub, eval_C, eval_pow, eval_X]
  linear_combination p.derivative.derivative.eval (G.L.weierstrassP z) *
    G.L.derivWeierstrassP_sq z hz

private lemma wp_iterated_even_odd (G : Frontier.Geometry) (p : Polynomial ℂ) (r : ℕ) :
    (∀ z : ℂ, z ∉ G.L.lattice →
      iteratedDeriv (2 * r) (fun w => p.eval (G.L.weierstrassP w)) z =
        ((wpJetStep G.L.g₂ G.L.g₃)^[r] p).eval (G.L.weierstrassP z)) ∧
    (∀ z : ℂ, z ∉ G.L.lattice →
      iteratedDeriv (2 * r + 1) (fun w => p.eval (G.L.weierstrassP w)) z =
        G.L.derivWeierstrassP z *
          ((wpJetStep G.L.g₂ G.L.g₃)^[r] p).derivative.eval (G.L.weierstrassP z)) := by
  induction r with
  | zero =>
    constructor
    · intro z hz
      rfl
    · intro z hz
      simpa only [Nat.mul_zero, zero_add, iteratedDeriv_one, Function.iterate_zero_apply]
        using deriv_wp_polynomial G p z hz
  | succ r ih =>
    have heven (z : ℂ) (hz : z ∉ G.L.lattice) :
        iteratedDeriv (2 * (r + 1)) (fun w => p.eval (G.L.weierstrassP w)) z =
          ((wpJetStep G.L.g₂ G.L.g₃)^[r + 1] p).eval (G.L.weierstrassP z) := by
      have hnear : iteratedDeriv (2 * r + 1) (fun w => p.eval (G.L.weierstrassP w))
          =ᶠ[𝓝 z] (fun w => G.L.derivWeierstrassP w *
            ((wpJetStep G.L.g₂ G.L.g₃)^[r] p).derivative.eval (G.L.weierstrassP w)) := by
        filter_upwards [G.L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
        exact ih.2 w hw
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega, iteratedDeriv_succ,
        hnear.deriv_eq, deriv_wp_weighted_polynomial G _ z hz,
        Function.iterate_succ_apply']
    refine ⟨heven, ?_⟩
    intro z hz
    have hnear : iteratedDeriv (2 * (r + 1)) (fun w => p.eval (G.L.weierstrassP w))
        =ᶠ[𝓝 z] (fun w => ((wpJetStep G.L.g₂ G.L.g₃)^[r + 1] p).eval
          (G.L.weierstrassP w)) := by
      filter_upwards [G.L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      exact heven w hw
    rw [iteratedDeriv_succ, hnear.deriv_eq, deriv_wp_polynomial G _ z hz]

private lemma chart_polynomial_jets (G : Frontier.Geometry) (z : ℂ)
    (hz : z ∉ G.L.lattice) (p : Polynomial ℂ) (j : ℕ) :
    MvPolynomial.eval (extensionChartCoordinates G.S 0 z)
        ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[j]
          (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) p)) =
      iteratedDeriv j (fun w => p.eval (G.L.weierstrassP w)) z := by
  have hzero : G.S (extensionChartDenominator 0) z ≠ 0 := by
    simpa [extensionChartDenominator] using (chart_regular_values G z hz).1
  rw [← ((G.hjets.2 0 (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) p) j).2 z hzero).1]
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [G.L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
  calc
    _ = Polynomial.aeval ((MvPolynomial.aeval (extensionChartCoordinates G.S 0 w))
        (MvPolynomial.X (1 : Fin 4))) p :=
      (Polynomial.aeval_algHom_apply (MvPolynomial.aeval (extensionChartCoordinates G.S 0 w))
        _ p).symm
    _ = _ := by simp [extensionChartCoordinates, (chart_regular_values G w hw).2.1]

theorem solution
    (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) (p : Polynomial ℂ) (j : ℕ) :
    let T : Polynomial ℂ → Polynomial ℂ := fun q =>
      (Polynomial.C 4 * Polynomial.X ^ 3 - Polynomial.C G.L.g₂ * Polynomial.X -
        Polynomial.C G.L.g₃) * q.derivative.derivative +
      (Polynomial.C 6 * Polynomial.X ^ 2 - Polynomial.C (G.L.g₂ / 2)) * q.derivative
    let q := T^[j / 2] p
    q.natDegree ≤ p.natDegree + j / 2 ∧
    MvPolynomial.eval (extensionChartCoordinates G.S 0 z)
      ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[j]
        (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) p)) =
      if j % 2 = 0 then q.eval (G.L.weierstrassP z)
      else G.L.derivWeierstrassP z * q.derivative.eval (G.L.weierstrassP z) := by
  refine ⟨wpJetStep_iterate_degree _ _ p (j / 2), ?_⟩
  change _ = if j % 2 = 0 then
    ((wpJetStep G.L.g₂ G.L.g₃)^[j / 2] p).eval (G.L.weierstrassP z)
    else G.L.derivWeierstrassP z *
      ((wpJetStep G.L.g₂ G.L.g₃)^[j / 2] p).derivative.eval (G.L.weierstrassP z)
  rw [chart_polynomial_jets G z hz p j]
  have h := wp_iterated_even_odd G p (j / 2)
  by_cases hj : j % 2 = 0
  · rw [if_pos hj]
    simpa only [show 2 * (j / 2) = j by omega] using h.1 z hz
  · rw [if_neg hj]
    simpa only [show 2 * (j / 2) + 1 = j by omega] using h.2 z hz
