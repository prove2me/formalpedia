-- Prove2me | solution 1 for ProbabilityTheory.charFun_map_levyJumpProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T04:23:14.665197+00:00
-- url     : https://prove2.me/submissions/1073893e-957f-4f84-95f6-d5400ab10dc9

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpProcess_sub
import Theorems.Thm_ProbabilityTheory_levyJumpProcess_zero_ae_eq
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω}
theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (levyJumpProcess hd hν b t)) ξ
      = Complex.exp (((t : ℝ) : ℂ) *
          (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  have h0 := levyJumpProcess_zero_ae_eq hd hν b
  have heq : (fun ω => levyJumpProcess hd hν b t ω -
        levyJumpProcess hd hν b 0 ω) =ᵐ[μ] levyJumpProcess hd hν b t := by
    filter_upwards [h0] with ω hω
    simp [hω]
  have hc := charFun_map_levyJumpProcess_sub hd hν b (show (0 : ℝ≥0) ≤ t from bot_le) ξ
  rw [Measure.map_congr heq] at hc
  simpa using hc
