-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.euclid_fifth_either_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:21:38.219987+00:00
-- url     : https://prove2.me/submissions/76c78913-51a4-4b92-af00-7d3b74afcff1

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_euclid_fifth_general
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_euclid_fifth_right

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
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧
      0 < F.a.side (F.b.pt t) * F.a.side F.b.one := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_general F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_pos hs hb⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_right F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_pos_of_neg_of_neg hs hb⟩
end ParallelPostulate.ThreeDimensions
