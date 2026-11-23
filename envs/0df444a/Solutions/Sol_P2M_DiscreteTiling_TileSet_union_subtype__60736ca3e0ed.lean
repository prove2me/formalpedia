-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_union_subtype__60736ca3e0ed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:14:46.163804+00:00
-- url     : https://prove2.me/submissions/91dd77a4-a575-432e-b238-e636ef23ea21

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_DiscreteTiling_TileSet_union_subtype
public import Theorems.Thm_DiscreteTiling_TileSet_union_of_mem_eq_iUnion


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution (t : TileSet ps ιₜ) (p : ιₜ → Prop) :
    ⋃ pt ∈ t.subtype p, (pt : Set X) = ⋃ (i) (_ : p i), (t i : Set X) := by
  rw [union_of_mem_eq_iUnion, union_subtype]
end DiscreteTiling.TileSet
