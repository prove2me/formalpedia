-- Prove2me | solution 1 for TwoDegenerateGraphs.not_erdos_146
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/e379fc1b-c5a2-45e4-83f9-d6c3091f6a89

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_eventually_constant_le_positive_nat_rpow
import Theorems.Thm_TwoDegenerateGraphs_twoDegenerateExtremalCounterexample

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ¬ DegeneracyConjectureStatement := by
  intro hconjecture
  obtain ⟨q, H, _hconnected, hbipartite, hdegenerate, _hdegree,
    c, ε, hc, hε, hlower⟩ := twoDegenerateExtremalCounterexample
  have hbigO := hconjecture 2 q H (by norm_num)
    hbipartite hdegenerate
  obtain ⟨C, hupper⟩ := Asymptotics.isBigO_iff.mp hbigO
  have hupper' :
      ∀ᶠ n : ℕ in Filter.atTop,
        (SimpleGraph.extremalNumber n H : ℝ) ≤
          C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
    filter_upwards [hupper] with n hn
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hextremal_nonneg :
        (0 : ℝ) ≤ (SimpleGraph.extremalNumber n H : ℝ) :=
      Nat.cast_nonneg _
    have hnormalized :
        (SimpleGraph.extremalNumber n H : ℝ) ≤
          C * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
        abs_of_nonneg (Real.rpow_nonneg hnnonneg _), Nat.cast_ofNat] using hn
    convert hnormalized using 1
    norm_num
  have hlarge :=
    CompactnessConjecture.eventually_constant_le_positive_nat_rpow
      (C + 1) c ε hc hε
  have himpossible : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hlower, hupper', hlarge,
      Filter.eventually_gt_atTop 0] with n hlow hupp hlarge_n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hscale : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hnreal _
    have hdecompose :
        c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) =
          (c * (n : ℝ) ^ ε) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Real.rpow_add hnreal]
      ring
    rw [hdecompose] at hlow
    have hscaled := mul_le_mul_of_nonneg_right hlarge_n hscale.le
    nlinarith
  exact himpossible.exists.elim (fun _ h => h)
end TwoDegenerateGraphs
