-- Prove2me | solution 1 for ParallelPostulate.Pairs.Figure.angle_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:24.529475+00:00
-- url     : https://prove2.me/submissions/251d036a-f5b3-4fb7-9a99-fee5cb08736e

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_norm_toE_pos_right
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_angle_pos_and_lt_pi
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_sin_angle_sum
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_b_one
public import Theorems.Thm_ParallelPostulate_Pairs_Figure_side_c_one


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
namespace _root_.ParallelPostulate.Pairs.Figure
theorem _root_.solution (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    sin (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir))
        * (‖toE F.b.dir‖ * ‖toE F.c.dir‖) = cross F.b.dir F.c.dir ∧
      0 < ‖toE F.b.dir‖ * ‖toE F.c.dir‖ ∧
      0 < angle (toE F.a.dir) (toE F.b.dir) ∧ angle (toE F.a.dir) (toE F.b.dir) < π ∧
      0 < angle (toE (-F.a.dir)) (toE F.c.dir) ∧ angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have hc' : cross (-F.a.dir) F.c.dir ≠ 0 := by
    have hneg : cross (-F.a.dir) F.c.dir = -cross F.a.dir F.c.dir := by
      simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hneg]
    exact neg_ne_zero.mpr hc.ne'
  obtain ⟨hβ0, hβπ⟩ := angle_pos_and_lt_pi hb.ne'
  obtain ⟨hγ0, hγπ⟩ := angle_pos_and_lt_pi hc'
  exact ⟨sin_angle_sum _ _ _ hb hc,
    mul_pos (norm_toE_pos_right hb.ne') (norm_toE_pos_right hc.ne'), hβ0, hβπ, hγ0, hγπ⟩
end _root_.ParallelPostulate.Pairs.Figure
end ParallelPostulate.ThreeDimensions
