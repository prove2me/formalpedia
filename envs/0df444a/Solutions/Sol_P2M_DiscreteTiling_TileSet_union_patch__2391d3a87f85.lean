-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_union_patch__2391d3a87f85
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:21:38.968612+00:00
-- url     : https://prove2.me/submissions/fbbcd228-caf5-4251-ae7d-89571575d7fb

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Theorems.Thm_P2M_DiscreteTiling_TileSet_union_subtype__60736ca3e0ed

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
theorem _root_.solution (t : TileSet ps ιₜ) (s : Set X) :
    ⋃ pt ∈ t.patch s, (pt : Set X) = ⋃ (i) (_ : (s ∩ t i).Nonempty), (t i : Set X) :=
  t.union_subtype' _
end DiscreteTiling.TileSet
