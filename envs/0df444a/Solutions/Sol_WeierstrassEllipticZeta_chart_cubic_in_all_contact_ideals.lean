-- Prove2me | solution 1 for WeierstrassEllipticZeta.chart_cubic_in_all_contact_ideals
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T19:41:39.569875+00:00
-- url     : https://prove2.me/submissions/3a9c7174-93e3-453c-acf2-7e0a754dbe89

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Tactic.LinearCombination

noncomputable section
open WeierstrassEllipticZeta
open scoped Classical

private lemma chart_regular_cubic (G : Frontier.Geometry) (z : ℂ)
    (hz : z ∉ G.L.lattice) :
    let v := extensionChartCoordinates G.S 0 z
    (v 2) ^ 2 = 4 * (v 1) ^ 3 - G.L.g₂ * v 1 - G.L.g₃ := by
  have hσ : G.D.sigma z ≠ 0 := by
    intro hzero
    obtain ⟨j, hj⟩ := G.hS_ne z
    rw [G.hS_value z hz j, hzero, zero_pow (by decide), zero_mul] at hj
    exact hj rfl
  simpa [extensionChartCoordinates, G.hS_value z hz, hσ] using
    G.L.derivWeierstrassP_sq z hz

theorem solution
    (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    let v := extensionChartCoordinates G.S 0 z
    let q := extensionChartCubic G.L.g₂ G.L.g₃ 0
    (v 2) ^ 2 = 4 * (v 1) ^ 3 - G.L.g₂ * v 1 - G.L.g₃ ∧
    ∀ N : ℕ, Ideal.span ({q} : Set (MvPolynomial (Fin 4) ℂ)) ≤
      extensionChartContactIdeal G.L.g₂ G.L.g₃ 0 v N := by
  let v := extensionChartCoordinates G.S 0 z
  let q := extensionChartCubic G.L.g₂ G.L.g₃ 0
  let D := extensionChartDerivation G.L.g₂ G.L.g₃ 0
  have hc : (v 2) ^ 2 = 4 * (v 1) ^ 3 - G.L.g₂ * v 1 - G.L.g₃ :=
    chart_regular_cubic G z hz
  have hev : MvPolynomial.eval v q = 0 := by
    simp [q, extensionChartCubic]
    linear_combination hc
  have hD : D q = 0 := G.hjets.1 0
  have hzero (k : ℕ) : D^[k] 0 = 0 := by
    induction k with
    | zero => rfl
    | succ k hk => rw [Function.iterate_succ_apply', hk, map_zero]
  refine ⟨hc, ?_⟩
  intro N
  apply Ideal.span_le.mpr
  rintro p (rfl : p = q)
  apply (G.hcontact.1 0 v N q).2
  intro k _
  cases k with
  | zero => exact hev
  | succ k =>
    change MvPolynomial.eval v (D^[k + 1] q) = 0
    rw [Function.iterate_succ_apply, hD, hzero, map_zero]
