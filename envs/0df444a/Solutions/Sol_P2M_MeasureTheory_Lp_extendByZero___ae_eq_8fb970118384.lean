-- Prove2me | solution 1 for P2M_MeasureTheory_Lp_extendByZero___ae_eq_8fb970118384
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:41:49.361934+00:00
-- url     : https://prove2.me/submissions/099a3b62-3a93-4ebe-acce-2e7fff75fa70

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
namespace MeasureTheory.Lp
theorem _root_.solution (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)
end MeasureTheory.Lp
