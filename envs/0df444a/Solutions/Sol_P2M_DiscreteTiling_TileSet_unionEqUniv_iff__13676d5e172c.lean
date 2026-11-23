-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_unionEqUniv_iff__13676d5e172c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:04.490243+00:00
-- url     : https://prove2.me/submissions/522c1922-8371-4461-bdb4-c4263a63f3c5

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Theorems.Thm_DiscreteTiling_TileSet_unionEqUniv_iff
public import Theorems.Thm_DiscreteTiling_TileSet_union_of_mem_eq_iUnion


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}
open DiscreteTiling.TileSet
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} :
    t.UnionEqUniv ↔ (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by
  rw [unionEqUniv_iff, union_of_mem_eq_iUnion]
end DiscreteTiling.TileSet
