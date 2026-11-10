-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat26_lintegral_one_sub_sinc_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:36:15.90684+00:00
-- url     : https://prove2.me/submissions/3940cd9a-82c4-47d2-a7e6-050768aea918

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_lintegral_one_sub_sinc_lt_top

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal ENNReal Real

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤ :=
  leanlevy_chat22_lintegral_one_sub_sinc_lt_top hν
