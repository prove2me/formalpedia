-- Prove2me | solution 1 for ShortWDRODual.Tight.supFn_lsc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:47:07.747915+00:00
-- url     : https://prove2.me/submissions/fcb7070f-a134-491f-ac0a-8555393b4eef

import Mathlib
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight

end ShortWDRODual.Tight

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Tight

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → ℝ) (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam) :
    LowerSemicontinuous (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) ∧
      Measurable (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by
  have hlsc : LowerSemicontinuous (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) := by
    unfold ShortWDRODual.Legendre.supFn pWassIntegrand
    refine lowerSemicontinuous_iSup fun x => ?_
    have hc : Continuous fun xh : X => ((f x - lam * dist xh x ^ p : ℝ) : EReal) := by
      refine continuous_coe_real_ereal.comp ?_
      refine continuous_const.sub (continuous_const.mul ?_)
      exact (continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr (by linarith))
    exact hc.lowerSemicontinuous
  exact ⟨hlsc, hlsc.measurable⟩

