-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_isTiling_iff__33c4d8525e7c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:39.280665+00:00
-- url     : https://prove2.me/submissions/fe8b4c84-a019-4eed-a5d6-8e90f9346556

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} : t.IsTiling ↔ t.Disjoint ∧ t.UnionEqUniv :=
  Iff.rfl
end DiscreteTiling.TileSet
