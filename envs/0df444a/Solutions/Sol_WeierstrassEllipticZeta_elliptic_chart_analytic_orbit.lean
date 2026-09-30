-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_chart_analytic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T19:25:22.19834+00:00
-- url     : https://prove2.me/submissions/a69743d2-21e7-4f0a-a1de-f593f44a4ec3

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_flow
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_chart_jets
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private lemma last_block_scaling (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → ℂ) (r : ℂ) :
    eval ![x 0, x 1, r * x 2, r * x 3, r * x 4, r * x 5, r * x 6] Q =
      r ^ n * eval x Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private lemma normalization_eval (c : Fin 2) (t : ℂ) (v : Fin 5 → ℂ)
    (hquad : v 0 * v 4 - v 2 * v 3 - 2 * v 1 ^ 2 = 0)
    (hv : v (extensionChartDenominator c) ≠ 0) (Q : MvPolynomial (Fin 7) ℂ) :
    eval (extensionChartCoordinates (fun j _ => v j) c t) (extensionChartNormalize c Q) =
      eval ![1, t, v 0 / v (extensionChartDenominator c),
        v 1 / v (extensionChartDenominator c), v 2 / v (extensionChartDenominator c),
        v 3 / v (extensionChartDenominator c), v 4 / v (extensionChartDenominator c)] Q := by
  have heval (f : Fin 4 → ℂ) :
      eval f (extensionChartNormalize c Q) =
        eval (fun i => eval f (extensionChartSubstitution c i)) Q := by
    exact comp_aeval_apply (extensionChartSubstitution c) (aeval f) Q
  rw [heval]
  apply congrArg (fun f : Fin 7 → ℂ => eval f Q)
  funext i
  fin_cases c
  · have hv0 : v 0 ≠ 0 := hv
    have hlast : v 2 / v 0 * (v 3 / v 0) + 2 * (v 1 / v 0) ^ 2 = v 4 / v 0 := by
      field_simp
      linear_combination -hquad
    fin_cases i <;> simp [extensionChartSubstitution, extensionChartCoordinates,
      extensionChartDenominator, hv0, hlast]
  · have hv2 : v 2 ≠ 0 := hv
    have hthird : v 0 / v 2 * (v 4 / v 2) - 2 * (v 1 / v 2) ^ 2 = v 3 / v 2 := by
      field_simp
      linear_combination hquad
    fin_cases i <;> simp [extensionChartSubstitution, extensionChartCoordinates,
      extensionChartDenominator, hv2, hthird]


end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun w : ℂ => eval
      ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) ≠ 0)
    (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
    ∃ φ : MvPolynomial (Fin 4) ℂ →ₐ[ℚ] (ℂ → ℂ),
      (∀ r w, φ r w = eval (extensionChartCoordinates S c w) r) ∧
      (∀ r, φ ((extensionChartDerivation L.g₂ L.g₃ c).restrictScalars ℚ r)
        =ᶠ[𝓝 z] deriv (φ r)) ∧
      AnalyticAt ℂ (φ (extensionChartNormalize c Q)) z ∧
      analyticOrderAt (φ (extensionChartNormalize c Q)) z ≠ ⊤ := by
  classical
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℚ] (ℂ → ℂ) :=
    AlgHom.pi fun w => (aeval (extensionChartCoordinates S c w)).restrictScalars ℚ
  have hφ (r : MvPolynomial (Fin 4) ℂ) (w : ℂ) :
      φ r w = eval (extensionChartCoordinates S c w) r := rfl
  have hU : IsOpen {w : ℂ | S (extensionChartDenominator c) w ≠ 0} :=
    (hS _).continuous.isOpen_preimage _ isOpen_ne
  have hquad (w : ℂ) : S 0 w * S 4 w - S 2 w * S 3 w - 2 * S 1 w ^ 2 = 0 := by
    have heq : (fun w => S 0 w * S 4 w - S 2 w * S 3 w - 2 * S 1 w ^ 2) =
        (0 : ℂ → ℂ) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (show AnalyticOnNhd ℂ _ Set.univ from fun w _ =>
          (((hS 0 w trivial).mul (hS 4 w trivial)).sub
            ((hS 2 w trivial).mul (hS 3 w trivial))).sub
            (analyticAt_const.mul ((hS 1 w trivial).pow 2)))
        (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
        (z₀ := L.ω₁ / 2)
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
        L.ω₁_div_two_notMem_lattice] with u hu
      simp [hS_value u hu]
      ring
    exact congrFun heq w
  have hscale (w : ℂ) (hw : S (extensionChartDenominator c) w ≠ 0) :
      eval ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q =
        S (extensionChartDenominator c) w ^ n * φ (extensionChartNormalize c Q) w := by
    rw [hφ]
    have hnorm := normalization_eval c w (fun j => S j w) (hquad w) hw Q
    change eval (extensionChartCoordinates S c w) (extensionChartNormalize c Q) = _ at hnorm
    rw [hnorm]
    have hs := last_block_scaling Q n hQ
      ![1, w, S 0 w / S (extensionChartDenominator c) w,
        S 1 w / S (extensionChartDenominator c) w,
        S 2 w / S (extensionChartDenominator c) w,
        S 3 w / S (extensionChartDenominator c) w,
        S 4 w / S (extensionChartDenominator c) w]
      (S (extensionChartDenominator c) w)
    simpa [mul_div_cancel₀, hw, mul_comm] using hs
  have ha : AnalyticAt ℂ (φ (extensionChartNormalize c Q)) z := by
    change AnalyticAt ℂ (fun w => eval (extensionChartCoordinates S c w)
      (extensionChartNormalize c Q)) z
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases c <;> fin_cases i <;> simp [extensionChartCoordinates]
    all_goals first | exact analyticAt_id |
      exact (hS _ z (Set.mem_univ _)).div (hS _ z (Set.mem_univ _)) hz
  refine ⟨φ, hφ, ?_, ha, ?_⟩
  · intro r
    have hj := elliptic_extension_projective_chart_jets L.g₂ L.g₃ S hS
      (elliptic_extension_projective_chart_flow L D S hS hS_value)
    filter_upwards [hU.mem_nhds hz] with w hw
    have he := ((hj.2 c r 1).2 w hw).1
    change eval (extensionChartCoordinates S c w)
      (extensionChartDerivation L.g₂ L.g₃ c r) =
        deriv (fun u => eval (extensionChartCoordinates S c u) r) w
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using he.symm
  · intro htop
    apply hne
    have hF : AnalyticOnNhd ℂ (fun w : ℂ => eval
        ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) Set.univ := by
      intro w _
      apply AnalyticAt.aeval_mvPolynomial
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_id
      all_goals exact hS _ w trivial
    apply AnalyticOnNhd.eq_of_eventuallyEq hF
      (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
      (z₀ := z)
    filter_upwards [hU.mem_nhds hz, analyticOrderAt_eq_top.mp htop] with w hw hzero
    change eval ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q = 0
    rw [hscale w hw, hzero, mul_zero]
