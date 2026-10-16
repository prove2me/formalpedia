-- Prove2me | solution 1 for PersPricingDist.PersonalA.cutoff_order
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:28:48.471312+00:00
-- url     : https://prove2.me/submissions/8466751b-ab25-4f90-a571-8c731ce2189b

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting
open PersPricingDist.PersonalA

theorem solution:
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, Model.vTilde s < Model.vCheck s := by
  intro s ⟨h0, h1⟩
  unfold Model.vTilde Model.vCheck
  have hlt : Real.sqrt (1 - s) < Real.sqrt ((1 - s) * (2 + 5 * s + s ^ 2) / (1 + 2 * s)) := by
    apply Real.sqrt_lt_sqrt (by linarith)
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  apply div_lt_div_of_pos_right _ (by linarith)
  apply mul_lt_mul_of_pos_left _ h0
  linarith
