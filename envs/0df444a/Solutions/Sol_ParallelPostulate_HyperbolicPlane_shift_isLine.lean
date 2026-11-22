-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_isLine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:28.638034+00:00
-- url     : https://prove2.me/submissions/1911dd03-4f58-4f2d-a227-e55f57ef086c

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_exists_within
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_openAlong
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_mem_points_of_side_eq_zero
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_side_eq_zero_of_mem
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_zero_mem


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {S : Set (K × K)} (hS : IsLine (plane κ) S) :
    IsLine (plane κ) (shift κ a w '' S) := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by
    rw [hw]
    ring
  have ha' : 0 < 1 + κ * (-a) ^ 2 := hw' ▸ hw2
  obtain ⟨M, hA, hB, hAB, rfl⟩ := hS.exists_within (plane_openAlong κ)
  have hDA := (shift_den_pos hκ ha hA).ne'
  have hDB := (shift_den_pos hκ ha hB).ne'
  have hτA : shift κ a w M.zero ∈ plane κ := shift_mem_plane hκ hw hw0 hA
  have hne : shift κ a w M.zero ≠ shift κ a w M.one := by
    intro h
    apply hAB
    have h' := congrArg (shift κ (-a) w) h
    rwa [shift_shift_neg hw hw0 hDA, shift_shift_neg hw hw0 hDB] at h'
  have hfactor : w * (1 + κ * a ^ 2) ≠ 0 := mul_ne_zero hw0 ha.ne'
  refine ⟨⟨shift κ a w M.zero, shift κ a w M.one⟩, hne, ?_,
    ⟨shift κ a w M.zero, M.zero, ⟨M.zero_mem, hA⟩, rfl⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨X, ⟨hXM, hX⟩, rfl⟩
    refine ⟨?_, shift_mem_plane hκ hw hw0 hX⟩
    apply Dim.mem_points_of_side_eq_zero _ hne
    have hDX := (shift_den_pos hκ ha hX).ne'
    have hside := M.side_eq_zero_of_mem hXM
    simp only [Dim.side, Dim.dir] at hside ⊢
    rw [shift_cross κ a w hDA hDB hDX, hside, mul_zero, zero_div]
  · rintro Y ⟨hYN, hY⟩
    have hDY := (shift_den_pos hκ ha' hY).ne'
    have hX : shift κ (-a) w Y ∈ plane κ := shift_mem_plane hκ hw' hw0 hY
    have hback : shift κ a w (shift κ (-a) w Y) = Y := by
      have h := shift_shift_neg hw' hw0 hDY
      rwa [neg_neg] at h
    have hDX := (shift_den_pos hκ ha hX).ne'
    refine ⟨shift κ (-a) w Y, ⟨?_, hX⟩, hback⟩
    apply Dim.mem_points_of_side_eq_zero _ hAB
    have hside := Dim.side_eq_zero_of_mem _ hYN
    rw [← hback] at hside
    simp only [Dim.side, Dim.dir] at hside ⊢
    rw [shift_cross κ a w hDA hDB hDX] at hside
    have hden : (1 - κ * a * M.zero.1) * (1 - κ * a * M.one.1)
        * (1 - κ * a * (shift κ (-a) w Y).1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hDA hDB) hDX
    rcases div_eq_zero_iff.mp hside with h | h
    · exact (mul_eq_zero.mp h).resolve_left hfactor
    · exact absurd h hden
end ParallelPostulate.HyperbolicPlane
