-- Prove2me | solution 1 for Thm67Support.integrable_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:09:12.224119+00:00
-- url     : https://prove2.me/submissions/7fb5dd79-337d-45fb-bb09-7d2694ccdf17

import Theorems.Thm_Thm67Support_realCoe_textbookIntegrable_iff
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
    Integrable (fun ω => (X ω).toReal) μ := by
  have h_realCoe : textbookIntegrable μ (fun ω => ((X ω).toReal : EReal)) := by
    obtain ⟨h_pos, h_neg⟩ := hX;
    constructor;
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) h_pos;
      cases h : X ω <;> simp +decide [ h, Def65Support.posPart ];
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) h_neg;
      cases h : X ω <;> simp +decide [ h, Def65Support.negPart ];
  convert realCoe_textbookIntegrable_iff _ |>.1 h_realCoe;
  fun_prop
end Thm67Support
