-- Prove2me | solution 1 for OracleStateHSP.fracOracle_queryComplexity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:30:36.419443+00:00
-- url     : https://prove2.me/submissions/c0f098b3-e15f-4cf0-ae61-d0353bbf6d87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OracleStateHSP_queryComplexity
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_fracOracle
import Theorems.Thm_OracleStateHSP_eq_60
import Theorems.Thm_OracleStateHSP_theorem_4_4
import Theorems.Thm_OracleStateHSP_fracOracle_unitary_prepares

open scoped ENNReal
open OracleStateHSP

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ r m : ℕ, 2 ≤ m →
      ENNReal.ofReal (c * ((m : ℝ) - 1) / Real.sqrt ε) ≤
          (queryComplexity (fun x : SimonInst m => fracOracle ε r x.fn)
            (fun x => x.period) : ℝ≥0∞) ∧
        (queryComplexity (fun x : SimonInst m => fracOracle ε r x.fn)
            (fun x => x.period) : ℝ≥0∞) ≤ ENNReal.ofReal (C * ((m : ℝ) - 1) / Real.sqrt ε) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, h60⟩ := OracleStateHSP.eq_60
  obtain ⟨c₁, c₂, hc₁, hc₁₂, h44⟩ := OracleStateHSP.theorem_4_4
  have hc₂ : 0 < c₂ := lt_trans hc₁ hc₁₂
  refine ⟨c₁ * c₀, c₂ * C₀, mul_pos hc₁ hc₀, mul_pos hc₂ hC₀, fun ε hε0 hε1 r m hm => ?_⟩
  have hunit : ∀ x : SimonInst m, fracOracle ε r x.fn ∈ Matrix.unitaryGroup (FlagQ r m) ℂ :=
    fun x => (OracleStateHSP.fracOracle_unitary_prepares ε hε0 hε1 r m x.fn).1
  obtain ⟨hQ_low, hQ_up⟩ :=
    h44 (SimonInst m) (V m) (FlagQ r m) (fun x => x.period) (fun x => fracOracle ε r x.fn) hunit
  obtain ⟨_, hγ_low, hγ_up⟩ := h60 ε hε0 hε1 r m hm
  constructor
  · have hmul : c₁ * c₀ * ((m : ℝ) - 1) / Real.sqrt ε =
        c₁ * (c₀ * ((m : ℝ) - 1) / Real.sqrt ε) := by ring
    rw [hmul, ENNReal.ofReal_mul hc₁.le]
    exact le_trans (by gcongr) hQ_low
  · have hmul : c₂ * C₀ * ((m : ℝ) - 1) / Real.sqrt ε =
        c₂ * (C₀ * ((m : ℝ) - 1) / Real.sqrt ε) := by ring
    rw [hmul, ENNReal.ofReal_mul hc₂.le]
    exact le_trans hQ_up (by gcongr)
