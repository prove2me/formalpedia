-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.meet_iff_angles_either_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:20:53.893907+00:00
-- url     : https://prove2.me/submissions/0f2e86dd-0996-4277-9a0a-bae1329b1b9d

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_side_iff_angles
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
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · exact meet_on_side_iff_angles F hb hc
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have h := meet_on_side_iff_angles F.reverse hb' hc'
    rw [F.reverse_angles] at h
    rw [← h]
    constructor
    · rintro ⟨t, u, ht, hu, e⟩
      exact ⟨u, t, hu, ht, e.symm⟩
    · rintro ⟨t, u, ht, hu, e⟩
      exact ⟨u, t, hu, ht, e.symm⟩
end ParallelPostulate.ThreeDimensions
