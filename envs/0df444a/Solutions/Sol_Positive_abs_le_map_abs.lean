-- Prove2me | solution 1 for Positive.abs_le_map_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:21.239816+00:00
-- url     : https://prove2.me/submissions/93973ae9-6c00-403b-9156-99e4e0bf9cf8

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Theorems.Thm_Positive_monotone_iff

set_option autoImplicit true
@[expose] public section
public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
open Positive
namespace Positive
theorem _root_.solution {f : X →ₗ[ℝ] Y} (hf : Positive f) (x : X) : |f x| ≤ f |x| := by
  rw [abs]
  apply sup_le
  · exact (monotone_iff.mpr hf) (by rw [abs]; exact le_sup_left)
  · have h : f (-x) ≤ f |x| := (monotone_iff.mpr hf) (by rw [abs]; exact le_sup_right)
    rwa [map_neg] at h
end Positive
