-- Prove2me | solution 1 for TailRiskSharing.ComonoConv.tail_parameter_upward_closed
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:06:52.674049+00:00
-- url     : https://prove2.me/submissions/9a6d1169-192d-44b5-aedc-39959c502a86

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Setting
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone

open MeasureTheory

namespace Aux_TRS_upward

lemma key (a p q : ℝ) (hpq : p ≤ q) :
    max (a - (1 - p)) 0 = max (max (a - (1 - q)) 0 - (q - p)) 0 := by
  rcases le_or_gt (1 - q) a with h | h
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ a - (1 - q))]
    ring_nf
  · rw [max_eq_right (by linarith : a - (1 - q) ≤ 0), max_eq_right (by linarith : a - (1 - p) ≤ 0),
      max_eq_right (by linarith : (0:ℝ) - (q - p) ≤ 0)]

end Aux_TRS_upward

open TailRiskSharing.ComonoConv in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : (Ω → ℝ) → ℝ) (p q : ℝ) (hp : 0 < p) (hpq : p ≤ q) (hq : q < 1)
    (hρ : IsTailRiskMeasure P L0 p ρ) :
    IsTailRiskMeasure P L0 q ρ := by
  intro X hX Y hY hXY
  apply hρ X hX Y hY
  intro x
  rw [Aux_TRS_upward.key _ p q hpq, Aux_TRS_upward.key (distFn P Y x) p q hpq, hXY x]
