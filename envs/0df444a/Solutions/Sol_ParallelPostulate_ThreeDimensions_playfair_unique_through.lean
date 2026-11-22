-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.playfair_unique_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:00.881049+00:00
-- url     : https://prove2.me/submissions/685418e8-b71e-4ee8-aeb4-99eedeba6ae2

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_iff_common_point
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_playfair_unique
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_dir_ne_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_rebase_dir
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_rebase_points
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_zero_ne_one_of_dir


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (L M M' : Dim K) (hL : L.zero ≠ L.one) (hM : M.zero ≠ M.one)
    (hM' : M'.zero ≠ M'.one) {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points)
    (h : ¬ Meet L M) (h' : ¬ Meet L M') : M.points = M'.points := by
  have hN : (M.rebase P).zero ≠ (M.rebase P).one :=
    (M.rebase P).zero_ne_one_of_dir (by rw [M.rebase_dir]; exact M.dir_ne_zero hM)
  have hN' : (M'.rebase P).zero ≠ (M'.rebase P).one :=
    (M'.rebase P).zero_ne_one_of_dir (by rw [M'.rebase_dir]; exact M'.dir_ne_zero hM')
  have hmeet : ¬ Meet L (M.rebase P) := by
    rw [meet_iff_common_point, M.rebase_points hP, ← meet_iff_common_point]
    exact h
  have hmeet' : ¬ Meet L (M'.rebase P) := by
    rw [meet_iff_common_point, M'.rebase_points hP', ← meet_iff_common_point]
    exact h'
  have hsame := playfair_unique L (M.rebase P) (M'.rebase P) hL hN hN' rfl hmeet hmeet'
  rwa [M.rebase_points hP, M'.rebase_points hP'] at hsame
end ParallelPostulate.ThreeDimensions
