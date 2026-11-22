-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.never_meet_either_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:20:41.87695+00:00
-- url     : https://prove2.me/submissions/530c282f-8c65-4079-8676-732a4293ef60

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_never_meet_general
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_angles
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_side


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · exact never_meet_general F hb hc hang t u
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have hang' := hang
    rw [← F.reverse_angles] at hang'
    intro e
    exact never_meet_general F.reverse hb' hc' hang' u t e.symm
end ParallelPostulate.ThreeDimensions
