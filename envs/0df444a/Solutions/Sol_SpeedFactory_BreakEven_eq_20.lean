-- Prove2me | solution 1 for SpeedFactory.BreakEven.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:11:04.530869+00:00
-- url     : https://prove2.me/submissions/52788a14-37fc-412a-9d18-1b8b9d30c4ef

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics
import Theorems.Thm_SpeedFactory_BreakEven_eq_19

open MeasureTheory ProbabilityTheory
open SpeedFactory.BreakEven

theorem solution (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d)
    (i0 j0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    ∀ γ ∈ Set.Ioc (0 : ℝ) 1,
      (costTBS M γ α i0 P d < costOUT M j0 pipe0 P d ↔ pMinus M α γ < M.p) := by
  intro γ hγ
  have h19 := SpeedFactory.BreakEven.eq_19 M hM hα P d hd i0 j0 pipe0 γ ⟨hγ.1.le, hγ.2⟩
  have hμ : 0 < M.μ := hM.1
  have hμγ : 0 < M.μ * γ := mul_pos hμ hγ.1
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (M.h + M.b) * (sigmaI M α - sigmaIS M) * stdNormalPDF (zi M)
      + M.u * M.m * sigmaQ M α * stdNormalPDF (zq M) := ⟨_, rfl⟩
  have hpm : pMinus M α γ = K / (M.μ * γ) + M.u := by
    simp only [pMinus, hK]; field_simp
  rw [← hK] at h19
  rw [hpm, ← sub_neg, h19]
  constructor
  · intro h
    have : K / (M.μ * γ) < M.p - M.u := by
      rw [div_lt_iff₀ hμγ]; nlinarith
    linarith
  · intro h
    have : K / (M.μ * γ) < M.p - M.u := by linarith
    rw [div_lt_iff₀ hμγ] at this
    nlinarith
