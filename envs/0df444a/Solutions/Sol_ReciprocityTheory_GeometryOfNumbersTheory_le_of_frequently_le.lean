-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.le_of_frequently_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:21.644098+00:00
-- url     : https://prove2.me/submissions/36b9a68b-327a-4e9b-95b9-3874849ab513

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_DefectSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Topology Asymptotics
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) (chi₁ chi₂ e : ℕ → ℝ) (t₁ t₂ s : ℝ)
    (h₁ : hsDefect D chi₁ t₁ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (h₂ : hsDefect D chi₂ t₂ =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (he : e =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1))
    (hle : ∃ᶠ n : ℕ in atTop,
      chi₁ n ≤ chi₂ n + s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) + e n) :
    t₁ ≤ t₂ + s := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  set ε : ℝ := (t₁ - t₂ - s) / ((D + 1).factorial : ℝ) with hε_def
  have hε : 0 < ε := div_pos (by linarith) hF
  have hb := ((h₁.sub h₂).sub he).def (half_pos hε)
  obtain ⟨n, hn, hb', h1⟩ := (hle.and_eventually (hb.and (eventually_ge_atTop 1))).exists
  have hP : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h1
    positivity
  simp only [Real.norm_eq_abs, abs_of_pos hP] at hb'
  have hb2 := (abs_le.mp hb').1
  unfold hsDefect at hb2
  have key : ε * (n : ℝ) ^ (D + 1) = t₁ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)
      - t₂ * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)
      - s * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by
    rw [hε_def]; field_simp
  have : 0 < ε / 2 * (n : ℝ) ^ (D + 1) := by positivity
  linarith
end ReciprocityTheory.GeometryOfNumbersTheory
