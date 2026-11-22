-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.euclid_fifth_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:20:41.404545+00:00
-- url     : https://prove2.me/submissions/4d1aa7ec-33a4-4596-9520-57490e82a481

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
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hc
  have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hb
  have hang' := hang
  rw [← F.reverse_angles] at hang'
  obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_general F.reverse hb' hc' hang'
  have e' : F.b.pt u = F.c.pt t := e.symm
  refine ⟨u, t, hu, ht, e', ?_⟩
  rw [F.reverse_side] at hs
  rw [e']
  exact neg_pos.mp hs
end ParallelPostulate.ThreeDimensions
