-- Prove2me | solution 1 for SpeedFactory.BreakEven.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:11:05.298857+00:00
-- url     : https://prove2.me/submissions/2ad13c3b-206c-4396-963f-c922e1917528

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics
import Theorems.Thm_SpeedFactory_BreakEven_proposition_1

open MeasureTheory ProbabilityTheory
open SpeedFactory.BreakEven

theorem solution (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) :
    (M.p < M.u → ∀ γ ∈ Set.Ioc (0 : ℝ) 1, costTBS M 0 α i0 P d < costTBS M γ α i0 P d) ∧
    (M.u < M.p → ∀ γ ∈ Set.Ico (0 : ℝ) 1,
      costTBS M 1 α i0 P d < costTBS M γ α i0 P d) := by
  have hμ : 0 < M.μ := hM.1
  have hc : ∀ γ ∈ Set.Icc (0 : ℝ) 1, costTBS M γ α i0 P d =
      sigmaI M α * (M.h + M.b) * stdNormalPDF (zi M)
      + sigmaQ M α * M.u * M.m * stdNormalPDF (zq M) + ((M.u - M.p) * γ + M.p) * M.μ := by
    intro γ hγ
    have h1 := SpeedFactory.BreakEven.proposition_1 M hM hγ hα P d hd i0
    simp only at h1
    exact h1.2.2.2.1.1.csInf_eq
  refine ⟨fun hpu γ hγ => ?_, fun hup γ hγ => ?_⟩
  · rw [hc 0 ⟨le_refl _, zero_le_one⟩, hc γ ⟨hγ.1.le, hγ.2⟩]
    have : 0 < (M.u - M.p) * γ * M.μ := mul_pos (mul_pos (by linarith) hγ.1) hμ
    nlinarith
  · rw [hc 1 ⟨zero_le_one, le_refl _⟩, hc γ ⟨hγ.1, hγ.2.le⟩]
    have : 0 < (M.p - M.u) * (1 - γ) * M.μ := mul_pos (mul_pos (by linarith) (by linarith [hγ.2])) hμ
    nlinarith
