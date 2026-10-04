-- Prove2me | solution 1 for TimeChange.continuous_inverse_clock_family
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T14:58:11.148437+00:00
-- url     : https://prove2.me/submissions/1f32013e-d528-43de-86d7-d48091ebaae1

import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem solution {S : Type*} [TopologicalSpace S]
    (c : S → (ℝ ≃o ℝ)) (hc : Continuous (fun p : ℝ × S => c p.2 p.1)) :
    Continuous (fun p : ℝ × S => (c p.2).symm p.1) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  constructor
  · have h := isOpen_lt
      (hc.comp ((continuous_const : Continuous (fun _ : ℝ × S => a)).prodMk continuous_snd))
      continuous_fst
    convert h using 1
    ext p
    exact (c p.2).lt_symm_apply
  · have h := isOpen_lt continuous_fst
      (hc.comp ((continuous_const : Continuous (fun _ : ℝ × S => a)).prodMk continuous_snd))
    convert h using 1
    ext p
    exact (c p.2).symm_apply_lt
