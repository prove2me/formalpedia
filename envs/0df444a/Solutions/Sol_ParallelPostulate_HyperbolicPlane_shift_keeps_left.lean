-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_keeps_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:28.100672+00:00
-- url     : https://prove2.me/submissions/5fed982d-ab26-45b6-930f-c7c014deadd3

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_cross

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : 0 < w)
    {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hC : C ∈ plane κ) :
    (0 < cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) ↔
      0 < cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) < 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) < 0) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) = 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) = 0) := by
  have ha : 0 < 1 + κ * a ^ 2 := by
    rw [← hw]
    exact pow_pos hw0 2
  have hDA := shift_den_pos hκ ha hA
  have hDB := shift_den_pos hκ ha hB
  have hDC := shift_den_pos hκ ha hC
  have hden : 0 < (1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1) :=
    mul_pos (mul_pos hDA hDB) hDC
  have hfac : 0 < w * (1 + κ * a ^ 2) := mul_pos hw0 ha
  have hr : 0 < w * (1 + κ * a ^ 2)
      / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := div_pos hfac hden
  rw [shift_cross κ a w hDA.ne' hDB.ne' hDC.ne', mul_div_right_comm]
  refine ⟨mul_pos_iff_of_pos_left hr, ?_, ?_⟩
  · constructor
    · intro h
      by_contra hcon
      exact absurd h (not_lt.mpr (mul_nonneg hr.le (not_lt.mp hcon)))
    · intro h
      exact mul_neg_of_pos_of_neg hr h
  · constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left hr.ne'
    · intro h
      rw [h, mul_zero]
end ParallelPostulate.HyperbolicPlane
