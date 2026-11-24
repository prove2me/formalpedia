-- Prove2me | solution 1 for SensitivityGraphPopulation.minimumEdges_copy_cost
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:31:37.413142+00:00
-- url     : https://prove2.me/submissions/16388f05-8346-4367-99e9-3d8743d136f1

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_IntegralGraphPopulation
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_SensitivityGraphPopulation_minimumEdges_succ

namespace SensitivityGraphPopulation
end SensitivityGraphPopulation

section


/-! Discrete convexity of the exact minimum-edge function. -/
namespace SensitivityGraphPopulation

noncomputable section
open scoped Classical
set_option autoImplicit false





theorem minimumEdges_step_upper (a b alpha m : ℕ) (hpos : 0 < alpha)
    (hab : a ≤ b) (hb : b ≤ (m + 1) * alpha) :
    minimumEdges b alpha ≤ minimumEdges a alpha + m * (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hb' : b ≤ (m + 1) * alpha := by omega
    have hdiv : b / alpha ≤ m := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hpos).mpr
      simpa only [Nat.succ_eq_add_one] using
        (show b < (m + 1) * alpha from by omega)
    rw [minimumEdges_succ b alpha hpos]
    have hi := ih hb'
    have hsub : b + 1 - a = b - a + 1 := by omega
    rw [hsub]
    nlinarith

theorem minimumEdges_step_lower (a b alpha m : ℕ) (hpos : 0 < alpha)
    (hab : a ≤ b) (ha : m * alpha ≤ a) :
    minimumEdges a alpha + m * (b - a) ≤ minimumEdges b alpha := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hdiv : m ≤ b / alpha := by
      apply (Nat.le_div_iff_mul_le hpos).mpr
      exact ha.trans hab
    rw [minimumEdges_succ b alpha hpos]
    have hsub : b + 1 - a = b - a + 1 := by omega
    rw [hsub]
    nlinarith






end
end SensitivityGraphPopulation

end

/-! Discrete convexity of the exact minimum-edge function. -/
open SensitivityGraphPopulation
open scoped Classical
set_option autoImplicit false

theorem solution (size outgoing alpha marks : ℕ) (hpos : 0 < alpha) :
    let best := size - (marks + 1) * alpha
    marks * best + minimumEdges (size - best) alpha ≤
      marks * outgoing + minimumEdges (size - outgoing) alpha := by
  dsimp
  let best := size - (marks + 1) * alpha
  have hbest : best ≤ size := Nat.sub_le _ _
  by_cases hout : outgoing ≤ best
  · by_cases hz : best = 0
    · have ho : outgoing = 0 := by omega
      subst outgoing
      change marks * best + minimumEdges (size - best) alpha ≤ _
      simp [hz]
    have hsize : (marks + 1) * alpha ≤ size := by
      unfold best at hz
      omega
    have hbase : size - best = (marks + 1) * alpha := by unfold best; omega
    have hstep := minimumEdges_step_lower (size - best) (size - outgoing) alpha marks
      hpos (by omega) (by rw [hbase]; nlinarith)
    have hdiff : size - outgoing - (size - best) = best - outgoing := by omega
    rw [hdiff] at hstep
    have hsum : outgoing + (best - outgoing) = best := Nat.add_sub_of_le hout
    dsimp [best] at hstep hsum ⊢
    nlinarith
  · by_cases ho : outgoing ≤ size
    · have hstep := minimumEdges_step_upper (size - outgoing) (size - best) alpha marks
        hpos (by omega) (by unfold best; omega)
      have hdiff : size - best - (size - outgoing) = outgoing - best := by omega
      rw [hdiff] at hstep
      have hsum : best + (outgoing - best) = outgoing := Nat.add_sub_of_le (by omega)
      dsimp [best] at hstep hsum ⊢
      nlinarith
    · have hstep := minimumEdges_step_upper 0 (size - best) alpha marks hpos (by omega)
        (by unfold best; omega)
      have hzero : minimumEdges 0 alpha = 0 := by simp [minimumEdges]
      rw [hzero] at hstep
      have hsub : size - outgoing = 0 := by omega
      rw [hsub, hzero]
      have hsum : best + (size - best) = size := Nat.add_sub_of_le hbest
      dsimp [best] at hstep hsum ⊢
      nlinarith
