-- Prove2me | solution 1 for Thm67Support.textbookIntegrable_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:28:02.429089+00:00
-- url     : https://prove2.me/submissions/d25e6326-02af-4408-8897-bc313df87811

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
    {X Y : Ω → EReal} (h : X =ᵐ[μ] Y) :
    textbookIntegrable μ X ↔ textbookIntegrable μ Y := by
  constructor <;> intro h' <;> constructor;
  · refine' lt_of_le_of_lt _ h'.1;
    refine' MeasureTheory.lintegral_mono_ae _;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.posPart ] ;
  · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono_ae _ ) ( h'.2 );
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.negPart ] ;
  · have h_pos : Def65Support.posLIntegral μ X = Def65Support.posLIntegral μ Y := by
      apply MeasureTheory.lintegral_congr_ae;
      filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.posPart ] ;
    exact h_pos.symm ▸ h'.1;
  · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono_ae _ ) h'.2;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.negPart ] ;
end Thm67Support
