-- Prove2me | solution 1 for SpeedFactory.BreakEven.eq_19
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:09:03.546551+00:00
-- url     : https://prove2.me/submissions/f3c94920-b462-4258-80bc-c6795c252812

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics
import Theorems.Thm_SpeedFactory_BreakEven_proposition_1
import Theorems.Thm_SpeedFactory_BreakEven_eq_18

open MeasureTheory ProbabilityTheory
open SpeedFactory.BreakEven

theorem solution (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d)
    (i0 j0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      costTBS M γ α i0 P d - costOUT M j0 pipe0 P d
        = (M.h + M.b) * (sigmaI M α - sigmaIS M) * stdNormalPDF (zi M)
          + M.u * M.m * sigmaQ M α * stdNormalPDF (zq M) + M.μ * γ * (M.u - M.p) := by
  intro γ hγ
  have h1 := SpeedFactory.BreakEven.proposition_1 M hM hγ hα P d hd i0
  have h18 := SpeedFactory.BreakEven.eq_18 M hM P d hd j0 pipe0
  simp only at h1 h18
  have e1 : costTBS M γ α i0 P d = sigmaI M α * (M.h + M.b) * stdNormalPDF (zi M)
      + sigmaQ M α * M.u * M.m * stdNormalPDF (zq M) + ((M.u - M.p) * γ + M.p) * M.μ :=
    h1.2.2.2.1.1.csInf_eq
  have e2 : costOUT M j0 pipe0 P d = sigmaIS M * (M.h + M.b) * stdNormalPDF (zi M) + M.p * M.μ :=
    h18.1.csInf_eq
  rw [e1, e2]; ring
