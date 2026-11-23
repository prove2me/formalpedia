-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup__3557f4183e3f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T05:53:17.167978+00:00
-- url     : https://prove2.me/submissions/e47845ba-7e27-4c4d-b8ac-0d8b133db222

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
attribute [coe] tiles
namespace DiscreteTiling.TileSet
theorem _root_.solution {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t j) = t i := by
  rcases exists_smul_eq_of_mem_symmetryGroup i (inv_mem hg) with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simp [← hj]
end DiscreteTiling.TileSet
