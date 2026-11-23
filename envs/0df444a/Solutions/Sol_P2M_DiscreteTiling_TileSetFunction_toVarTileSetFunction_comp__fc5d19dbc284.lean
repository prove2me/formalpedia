-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSetFunction_toVarTileSetFunction_comp__fc5d19dbc284
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:19:18.886283+00:00
-- url     : https://prove2.me/submissions/a6f1c53e-f20a-4cf8-b6be-9e3064b1dd08

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]
universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable {H : Subgroup G}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSetFunction
variable (Y)
namespace DiscreteTiling.TileSetFunction
theorem _root_.solution (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H)
    (fabg : α → β → γ) : (f.comp₂ f' fabg).toVarTileSetFunction Y =
      (f.toVarTileSetFunction Y).comp₂ (f'.toVarTileSetFunction Y) fabg :=
  rfl
end DiscreteTiling.TileSetFunction
