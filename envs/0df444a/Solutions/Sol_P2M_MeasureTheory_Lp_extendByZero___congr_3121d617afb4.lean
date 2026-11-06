-- Prove2me | solution 1 for P2M_MeasureTheory_Lp_extendByZero___congr_3121d617afb4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:55.895098+00:00
-- url     : https://prove2.me/submissions/08ac15d9-dbe6-471f-bc0e-267b6ebf82d2

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Definitions.Def_RellichKondrachov_MeasureTheory_Function_LpSpace_Restrict
import Theorems.Thm_P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal
open MeasureTheory.Lp
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)
namespace MeasureTheory.Lp
theorem _root_.solution (hs₁ hs₂ : MeasurableSet s) :
    extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁ =
      extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂ := by
  -- `extendByZeroₗᵢ` is characterized by its pointwise representative.
  refine LinearIsometry.toLinearMap_injective ?_
  refine LinearMap.ext ?_
  intro f
  refine MeasureTheory.Lp.ext (E := E) (p := p) (μ := μ) ?_
  have h₁ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₁) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₁) f
  have h₂ :
      ((extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs₂) f : α → E) =ᵐ[μ]
        s.indicator fun x : α => f x :=
    extendByZeroₗᵢ_ae_eq (μ := μ) (E := E) (p := p) (s := s) (hs := hs₂) f
  exact h₁.trans h₂.symm
end MeasureTheory.Lp
