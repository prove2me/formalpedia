-- Prove2me | solution 1 for Thm67Support.ae_eq_realCoe_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:04:51.97995+00:00
-- url     : https://prove2.me/submissions/cdea585c-6a29-45b8-8f45-35660c95acdc

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
namespace Thm67Support
end Thm67Support
section Thm67Support
open Thm67Support

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → EReal} (hXm : Measurable X) (hX : textbookIntegrable μ X) :
    X =ᵐ[μ] fun ω => ((X ω).toReal : EReal) := by
  have h_pos : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := by
    convert MeasureTheory.ae_lt_top ( hXm.ereal_toENNReal ) _ using 1;
    · ext ω; cases h : X ω <;> simp +decide;
    · exact hX.1.ne
  have h_neg : ∀ᵐ ω ∂μ, X ω ≠ ⊥ := by
    have h_neg_finite := MeasureTheory.ae_lt_top (hXm.neg.ereal_toENNReal) hX.2.ne
    filter_upwards [h_neg_finite] with ω hω
    cases hx : X ω <;> simp_all [hx]
  filter_upwards [ h_pos, h_neg ] with ω hω₁ hω₂ using by cases h : X ω <;> aesop;
end Thm67Support
