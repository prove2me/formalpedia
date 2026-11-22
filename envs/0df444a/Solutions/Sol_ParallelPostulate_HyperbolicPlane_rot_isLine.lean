-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.rot_isLine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:37.592573+00:00
-- url     : https://prove2.me/submissions/c989f1ac-106d-469a-a460-dad641e240b1

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_pt
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
omit [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {S : Set (K × K)}
    (hS : IsLine (plane κ) S) : IsLine (plane κ) (rot c s '' S) := by
  obtain ⟨M, hM, rfl, A, hAM, hA⟩ := hS
  have hne : rot c s M.zero ≠ rot c s M.one := by
    intro h'
    apply hM
    have h'' := congrArg (rot c (-s)) h'
    rwa [rot_rot_neg h, rot_rot_neg h] at h''
  refine ⟨⟨rot c s M.zero, rot c s M.one⟩, hne, ?_, ⟨rot c s A, A, ⟨hAM, hA⟩, rfl⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨X, ⟨⟨t, rfl⟩, hX⟩, rfl⟩
    exact ⟨⟨t, (rot_pt c s M t).symm⟩, (rot_mem_plane h).mpr hX⟩
  · rintro Y ⟨⟨t, rfl⟩, hY⟩
    rw [← rot_pt] at hY
    exact ⟨M.pt t, ⟨⟨t, rfl⟩, (rot_mem_plane h).mp hY⟩, rot_pt c s M t⟩
end ParallelPostulate.HyperbolicPlane
