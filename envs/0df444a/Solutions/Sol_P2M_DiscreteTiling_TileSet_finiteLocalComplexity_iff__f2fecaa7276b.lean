-- Prove2me | solution 1 for P2M_DiscreteTiling_TileSet_finiteLocalComplexity_iff__f2fecaa7276b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:22:00.556789+00:00
-- url     : https://prove2.me/submissions/1cc32a0f-8332-4c14-9b1e-641766d89b7a

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_FiniteLocalComplexity
public import Theorems.Thm_DiscreteTiling_TileSet_finiteLocalComplexity_iff
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_apply
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_const
public import Theorems.Thm_DiscreteTiling_TileSetFunction_toVarTileSetFunction_toTileSetFunction
public import Theorems.Thm_DiscreteTiling_TileSet_card_reindex_of_equivLike
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_empty
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_of_subsingleton
public import Theorems.Thm_DiscreteTiling_TileSet_finiteDistinctIntersectionsOn_univ_iff
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.card_reindex_of_equivLike
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_empty
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_of_subsingleton
attribute [local simp] DiscreteTiling.TileSet.finiteDistinctIntersectionsOn_univ_iff
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_apply
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_const
attribute [local simp] DiscreteTiling.TileSetFunction.toVarTileSetFunction_toTileSetFunction



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
theorem _root_.solution {H : Subgroup G} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexity H ↔
      (Set.range (fun x ↦ Quotient.mk (MulAction.orbitRel H (X × TileSetCard ps))
        (x, (t.patch {x}).card))).Finite := by
  rw [finiteLocalComplexity_iff]
  refine (Set.BijOn.finite_iff_finite (f := ?_) ⟨?_, ?_, ?_⟩).symm
  · refine fun q ↦ q.liftOn' (fun x ↦ ⟦({x.1}, x.2)⟧) fun y₁ y₂ h ↦ ?_
    rw [Quotient.eq'']
    obtain ⟨g, h⟩ := h
    refine ⟨g, ?_⟩
    rw [Prod.ext_iff] at h
    simp only [Prod.smul_fst, Prod.smul_snd] at h
    simpa using h
  · simp
  · intro q₁ hq₁ q₂ hq₂ h
    obtain ⟨x₁, rfl⟩ := hq₁
    obtain ⟨x₂, rfl⟩ := hq₂
    simp only [Quotient.liftOn'_mk'', Quotient.eq''] at h
    obtain ⟨g, h⟩ := h
    rw [Quotient.eq'']
    refine ⟨g, ?_⟩
    simpa using h
  · intro q hq
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and] at hq
    obtain ⟨x, rfl⟩ := hq
    simp
end DiscreteTiling.TileSet
