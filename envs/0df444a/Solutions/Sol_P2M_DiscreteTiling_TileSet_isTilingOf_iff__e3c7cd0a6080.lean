-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_isTilingOf_iff__e3c7cd0a6080
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:25.151228+00:00
-- url     : https://prove2.me/submissions/2a89fbce-5e34-4ba2-a78f-c9ee5f310507

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
theorem _root_.solution {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    t.Disjoint ∧ t.UnionEq s :=
  Iff.rfl
end DiscreteTiling.TileSet
