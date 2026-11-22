-- Prove2me | solution 1 for OrderIdeal.gaugeNorm_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:28:53.365636+00:00
-- url     : https://prove2.me/submissions/e4dca9e7-0547-4dee-9097-fa8c4b593345

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_OrderIdeal_gaugeNorm_le_of_abs_le

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)
namespace OrderIdeal
theorem _root_.solution [IsVLArchimedean X] {x : X} (hx : x ∈ principal a) :
    gaugeNorm a x ≤ 1 ↔ |x| ≤ |a| := by
  constructor
  · intro h
    calc |x| ≤ gaugeNorm a x • |a| := abs_le_gaugeNorm_smul_abs a hx
      _ ≤ 1 • |a| := smul_le_smul_of_nonneg_right h (abs_nonneg a)
      _ = |a| := one_smul ℝ |a|
  · intro h
    exact gaugeNorm_le_of_abs_le a one_pos.le (by rwa [one_smul])
end OrderIdeal
