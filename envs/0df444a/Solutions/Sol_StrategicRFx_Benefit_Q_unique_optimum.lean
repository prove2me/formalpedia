-- Prove2me | solution 1 for StrategicRFx.Benefit.Q_unique_optimum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:13:44.792557+00:00
-- url     : https://prove2.me/submissions/5261a167-0c76-436e-b076-2f8f6838b677

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

open StrategicRFx.Benefit

lemma rfx5_Qbound (θ0 θ1 a0 a1 x0 x1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1)
    (hq0 : x0 ≤ θ0 * max (a0 - x1) 0) (hq1 : x1 ≤ θ1 * max (a1 - x0) 0) :
    x0 + x1 ≤ F0 + F1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - x1) with hC | hC <;>
  rcases le_total 0 (a1 - x0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]


set_option maxHeartbeats 4000000 in
lemma rfx5_Quniq (θ0 θ1 a0 a1 x0 x1 F0 F1 : ℝ) (h0 : 0 < θ0) (h0' : θ0 < 1) (h1 : 0 < θ1)
    (h1' : θ1 < 1) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hF0 : F0 = θ0 * max (a0 - F1) 0) (hF1 : F1 = θ1 * max (a1 - F0) 0)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1)
    (hq0 : x0 ≤ θ0 * max (a0 - x1) 0) (hq1 : x1 ≤ θ1 * max (a1 - x0) 0)
    (hs : x0 + x1 = F0 + F1) : x0 = F0 ∧ x1 = F1 := by
  have h01 : 0 < 1 - θ0 * θ1 := by nlinarith
  rcases le_total 0 (a0 - F1) with hA | hA <;>
  rcases le_total 0 (a1 - F0) with hB | hB <;>
  rcases le_total 0 (a0 - x1) with hC | hC <;>
  rcases le_total 0 (a1 - x0) with hD | hD <;>
  simp only [max_eq_left hA, max_eq_right hA, max_eq_left hB, max_eq_right hB,
    max_eq_left hC, max_eq_right hC, max_eq_left hD, max_eq_right hD, mul_zero] at hF0 hF1 hq0 hq1 <;>
  constructor <;>
  nlinarith [mul_le_mul_of_nonneg_left hq0 (by linarith : (0:ℝ) ≤ 1 - θ1),
    mul_le_mul_of_nonneg_left hq1 (by linarith : (0:ℝ) ≤ 1 - θ0),
    mul_pos h0 h1, mul_pos h0 ha0, mul_pos h1 ha1, mul_pos (by linarith : (0:ℝ) < 1 - θ1) h0,
    mul_pos (by linarith : (0:ℝ) < 1 - θ0) h1]

theorem solution (P : Params) (hP : Standing P) (πF : Fin 2 → ℝ)
    (hF : ∀ i, πF i = P.θ i * max (P.Pi - πF (other i) - P.PiEx i) 0) :
    QFeasible P πF ∧
      ∀ π : Fin 2 → ℝ, QFeasible P π →
        P.Pi - πF 0 - πF 1 ≤ P.Pi - π 0 - π 1 ∧
          (P.Pi - π 0 - π 1 = P.Pi - πF 0 - πF 1 → π = πF) := by
  have o0 : other 0 = 1 := by decide
  have o1 : other 1 = 0 := by decide
  refine ⟨fun i => ⟨?_, (hF i).le⟩, fun π hπ => ?_⟩
  · rw [hF i]; exact mul_nonneg (hP.θ_pos i).le (le_max_right _ _)
  have hF0 := hF 0
  have hF1 := hF 1
  rw [o0, show P.Pi - πF 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - πF 1 by ring] at hF0
  rw [o1, show P.Pi - πF 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - πF 0 by ring] at hF1
  have ha0 : 0 < P.Pi - P.PiEx 0 := by linarith [hP.PiEx_lt 0]
  have ha1 : 0 < P.Pi - P.PiEx 1 := by linarith [hP.PiEx_lt 1]
  obtain ⟨hx0, hq0⟩ := hπ 0
  obtain ⟨hx1, hq1⟩ := hπ 1
  rw [o0, show P.Pi - π 1 - P.PiEx 0 = (P.Pi - P.PiEx 0) - π 1 by ring] at hq0
  rw [o1, show P.Pi - π 0 - P.PiEx 1 = (P.Pi - P.PiEx 1) - π 0 by ring] at hq1
  have h1 := rfx5_Qbound (P.θ 0) (P.θ 1) _ _ (π 0) (π 1) (πF 0) (πF 1) (hP.θ_pos 0)
    (hP.θ_lt_one 0) (hP.θ_pos 1) (hP.θ_lt_one 1) ha0 ha1 hF0 hF1 hx0 hx1 hq0 hq1
  refine ⟨by linarith, fun he => ?_⟩
  obtain ⟨e0, e1⟩ := rfx5_Quniq (P.θ 0) (P.θ 1) _ _ (π 0) (π 1) (πF 0) (πF 1) (hP.θ_pos 0)
    (hP.θ_lt_one 0) (hP.θ_pos 1) (hP.θ_lt_one 1) ha0 ha1 hF0 hF1 hx0 hx1 hq0 hq1 (by linarith)
  funext i
  fin_cases i
  · exact e0
  · exact e1
