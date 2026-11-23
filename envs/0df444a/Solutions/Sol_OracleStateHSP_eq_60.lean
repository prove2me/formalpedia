-- Prove2me | solution 1 for OracleStateHSP.eq_60
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:24:47.242479+00:00
-- url     : https://prove2.me/submissions/68300a06-e4d2-4e84-a8d5-12792fd48d39
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OracleStateHSP_answerNe
import Definitions.Def_OracleStateHSP_relGamma2
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_fracOracle
import Theorems.Thm_OracleStateHSP_eq_58
import Theorems.Thm_OracleStateHSP_fact_4_5
import Theorems.Thm_OracleStateHSP_eq_59

open scoped ENNReal
open OracleStateHSP

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ r m : ℕ, 2 ≤ m →
      relGamma2 (answerNe fun x : SimonInst m => x.period)
          (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) =
        relGamma2 (answerNe fun x : SimonInst m => x.period)
          (fun x y => fracOracle 1 r x.fn - fracOracle 1 r y.fn) / ENNReal.ofReal (Real.sqrt ε) ∧
      ENNReal.ofReal (c * ((m : ℝ) - 1) / Real.sqrt ε) ≤
          relGamma2 (answerNe fun x : SimonInst m => x.period)
            (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) ∧
      relGamma2 (answerNe fun x : SimonInst m => x.period)
          (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) ≤
        ENNReal.ofReal (C * ((m : ℝ) - 1) / Real.sqrt ε) := by
  obtain ⟨c, C, hc, hC, h59⟩ := OracleStateHSP.eq_59
  refine ⟨c, C, hc, hC, fun ε hε0 hε1 r m hm => ?_⟩
  have hs_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε0
  have hs_ne : (Real.sqrt ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_pos.ne'
  have hdiff : (fun x y : SimonInst m => fracOracle ε r x.fn - fracOracle ε r y.fn) =
      (fun x y : SimonInst m => (Real.sqrt ε : ℂ) • (fracOracle 1 r x.fn - fracOracle 1 r y.fn)) := by
    funext x y
    exact (OracleStateHSP.eq_58 ε hε0 hε1 r m x.fn y.fn).2
  have heq : relGamma2 (answerNe fun x : SimonInst m => x.period)
        (fun x y => fracOracle ε r x.fn - fracOracle ε r y.fn) =
      relGamma2 (answerNe fun x : SimonInst m => x.period)
        (fun x y => fracOracle 1 r x.fn - fracOracle 1 r y.fn) / ENNReal.ofReal (Real.sqrt ε) := by
    rw [hdiff, OracleStateHSP.fact_4_5 _ _ (Real.sqrt ε : ℂ) hs_ne,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
  obtain ⟨hlow1, hup1⟩ := h59 r m hm
  refine ⟨heq, ?_, ?_⟩
  · rw [heq, ENNReal.ofReal_div_of_pos hs_pos]
    exact ENNReal.div_le_div_right hlow1 _
  · rw [heq, ENNReal.ofReal_div_of_pos hs_pos]
    exact ENNReal.div_le_div_right hup1 _
