-- Prove2me | solution 2 for P2M_MeasureTheory_Lp_extendByZero___congr_3121d617afb4
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:11:21.915883+00:00
-- url     : https://prove2.me/submissions/4da1e7fd-18b2-4b1a-8221-d61228646df8

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Definitions.Def_RellichKondrachov_MeasureTheory_Function_LpSpace_Restrict
set_option autoImplicit true
open MeasureTheory
open scoped ENNReal
open MeasureTheory.Lp
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

theorem solution (hs₁ hs₂ : MeasurableSet s) :
    extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁ =
      extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂ := by
  rfl
