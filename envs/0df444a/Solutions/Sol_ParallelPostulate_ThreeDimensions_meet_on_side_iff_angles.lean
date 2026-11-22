-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.meet_on_side_iff_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:44.845803+00:00
-- url     : https://prove2.me/submissions/f2a3e17c-202c-4b43-9fe1-28cb7667e811

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_side_iff
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_pos_of_angles
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_eq_zero_of_angles
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_neg_of_angles

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rw [meet_on_side_iff F hb hc]
  constructor
  · intro hpos
    rcases lt_trichotomy
        (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) π
      with h | h | h
    · exact h
    · have h0 := cross_eq_zero_of_angles F hb hc h
      rw [h0] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact absurd hpos (lt_asymm (cross_neg_of_angles F hb hc h))
  · exact cross_pos_of_angles F hb hc
end ParallelPostulate.ThreeDimensions
