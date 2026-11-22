-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.other_side_either_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:20:52.232912+00:00
-- url     : https://prove2.me/submissions/976ba9d1-aa6b-4a1d-a3fc-bb2f7e71210c

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_other_side_general
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
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧
      F.a.side (F.b.pt t) * F.a.side F.b.one < 0 := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := other_side_general F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_neg_of_neg_of_pos hs hb⟩
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have hang' := hang
    rw [← F.reverse_angles] at hang'
    obtain ⟨t, u, ht, hu, e, hs⟩ := other_side_general F.reverse hb' hc' hang'
    have e' : F.b.pt u = F.c.pt t := e.symm
    refine ⟨u, t, hu, ht, e', ?_⟩
    rw [F.reverse_side] at hs
    rw [e']
    exact mul_neg_of_pos_of_neg (neg_lt_zero.mp hs) hb
end ParallelPostulate.ThreeDimensions
