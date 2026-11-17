-- Prove2me | solution 1 for Thm67Support.textbookIntegral_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:05:00.958558+00:00
-- url     : https://prove2.me/submissions/2b7c70b3-0f62-4640-9111-61f959fc90e9

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
    textbookIntegral μ X = textbookIntegral μ Y := by
  unfold textbookIntegral;
  -- Since $X$ and $Y$ are equal almost everywhere, their positive and negative parts are also equal almost everywhere.
  have h_pos_eq : Def65Support.posLIntegral μ X = Def65Support.posLIntegral μ Y := by
    apply MeasureTheory.lintegral_congr_ae;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.posPart ] ;
  have h_neg_eq : Def65Support.negLIntegral μ X = Def65Support.negLIntegral μ Y := by
    apply MeasureTheory.lintegral_congr_ae;
    filter_upwards [ h ] with ω hω using by simp +decide [ hω, Def65Support.negPart ] ;
  aesop
end Thm67Support
