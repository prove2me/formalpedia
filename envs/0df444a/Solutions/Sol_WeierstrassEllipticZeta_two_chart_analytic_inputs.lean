-- Prove2me | solution 1 for WeierstrassEllipticZeta.two_chart_analytic_inputs
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T20:24:38.808182+00:00
-- url     : https://prove2.me/submissions/31c7913f-7741-4c27-914e-57ff21e1541b

import Theorems.Thm_TranscendenceTheory_projective_chart_vanishing_order
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartNormalization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open MvPolynomial Filter
open scoped Topology Classical
namespace WeierstrassEllipticZeta

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
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hquad : ∀ z, S 0 z * S 4 z - S 2 z * S 3 z - 2 * S 1 z ^ 2 = 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n T : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (Y : Set ℂ)
    (hfinite : ∃ (c : Fin 2) (z : ℂ), S (extensionChartDenominator c) z ≠ 0 ∧
      analyticOrderAt (fun w => eval (extensionChartCoordinates S c w)
        (extensionChartNormalize c Q)) z ≠ ⊤)
    (hhigh : ∀ z ∈ Y, ∃ c : Fin 2, S (extensionChartDenominator c) z ≠ 0 ∧
      (T : ℕ∞) ≤ analyticOrderAt (fun w => eval (extensionChartCoordinates S c w)
        (extensionChartNormalize c Q)) z) :
    (fun z : ℂ => eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 ∧
      ∀ z ∈ Y, ∀ j : Fin 5, S j z ≠ 0 →
        (T : ℕ∞) ≤ analyticOrderAt (fun w => eval
          ![1, w, S 0 w / S j w, S 1 w / S j w, S 2 w / S j w,
            S 3 w / S j w, S 4 w / S j w] Q) z := by
  have hproj (z : ℂ) (j : Fin 5) (hj : S j z ≠ 0) :
      analyticOrderAt (fun w => eval
        ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) z =
      analyticOrderAt (fun w => eval
        ![1, w, S 0 w / S j w, S 1 w / S j w, S 2 w / S j w,
          S 3 w / S j w, S 4 w / S j w] Q) z := by
    exact (TranscendenceTheory.projective_chart_vanishing_order
      ![fun _ => (1 : ℂ), fun w => w] S Q n hQ z j hj
      (by intro i; fin_cases i; exact analyticAt_const; exact analyticAt_id)
      (fun i => hS i z trivial)).2.2.1
  have hnorm (c : Fin 2) (z : ℂ) (hz : S (extensionChartDenominator c) z ≠ 0) :
      analyticOrderAt (fun w => eval
        ![1, w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q) z =
      analyticOrderAt (fun w => eval (extensionChartCoordinates S c w)
        (extensionChartNormalize c Q)) z := by
    rw [hproj z (extensionChartDenominator c) hz]
    apply analyticOrderAt_congr
    have hU : IsOpen {w : ℂ | S (extensionChartDenominator c) w ≠ 0} :=
      (hS _).continuous.isOpen_preimage _ isOpen_ne
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (normalization_eval c w (fun j => S j w) (hquad w) hw Q).symm
  constructor
  · obtain ⟨c, z, hz, hf⟩ := hfinite
    intro hzero
    apply hf
    rw [← hnorm c z hz, hzero]
    exact analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall (fun _ => rfl))
  · intro z hz j hj
    obtain ⟨c, hc, horder⟩ := hhigh z hz
    rwa [← hnorm c z hc, hproj z j hj] at horder
