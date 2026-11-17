-- Prove2me | solution 1 for complexTextbookIntegral_eq_some_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:37:49.430653+00:00
-- url     : https://prove2.me/submissions/b2c0aa98-ed1d-45bd-9e20-36ebe7c019c1

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
namespace Def66RealSupport
end Def66RealSupport

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : complexTextbookIntegrable μ Z) :
    ∃ w : ℂ, complexTextbookIntegral μ Z = some w := by
  classical
  refine ⟨Complex.ofReal
      (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).re : EReal))) +
    Complex.I *
      Complex.ofReal
        (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).im : EReal))), ?_⟩
  simp [complexTextbookIntegral, hZ]
