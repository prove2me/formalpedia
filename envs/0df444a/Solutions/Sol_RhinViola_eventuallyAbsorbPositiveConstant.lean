-- Prove2me | solution 1 for RhinViola.eventuallyAbsorbPositiveConstant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T11:07:57.079753+00:00
-- url     : https://prove2.me/submissions/b46e5aaa-b349-4b33-8d3b-0a26962f657c

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Filter

theorem solution
    (C E T : ℝ) (hC : 0 < C) (hET : E < T) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 0 < q →
      (q : ℝ) ^ (-T) < C * (q : ℝ) ^ (-E) := by
  have hgap : 0 < T - E := sub_pos.mpr hET
  have hlim : Tendsto (fun q : ℕ => (q : ℝ) ^ (T - E)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  obtain ⟨Q, hQ⟩ :=
    eventually_atTop.mp ((tendsto_atTop.1 hlim) (2 / C))
  refine ⟨Q, ?_⟩
  intro q hQq hq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  have hgrowth : 2 / C ≤ (q : ℝ) ^ (T - E) := hQ q hQq
  have hCne : C ≠ 0 := ne_of_gt hC
  have hfactor : 1 < C * (q : ℝ) ^ (T - E) := by
    have hs := mul_le_mul_of_nonneg_left hgrowth hC.le
    have htwo : C * (2 / C) = 2 := by
      field_simp [hCne]
    rw [htwo] at hs
    linarith
  have hpow :
      (q : ℝ) ^ (-T) * (q : ℝ) ^ (T - E) =
        (q : ℝ) ^ (-E) := by
    rw [← Real.rpow_add hqr]
    congr 1
    ring
  have hbase : 0 < (q : ℝ) ^ (-T) := by positivity
  calc
    (q : ℝ) ^ (-T) = (q : ℝ) ^ (-T) * 1 := by ring
    _ < (q : ℝ) ^ (-T) * (C * (q : ℝ) ^ (T - E)) :=
      mul_lt_mul_of_pos_left hfactor hbase
    _ = C * ((q : ℝ) ^ (-T) * (q : ℝ) ^ (T - E)) := by ring
    _ = C * (q : ℝ) ^ (-E) := by rw [hpow]
