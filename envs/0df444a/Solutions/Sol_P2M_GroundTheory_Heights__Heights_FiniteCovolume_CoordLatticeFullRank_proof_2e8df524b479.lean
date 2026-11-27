-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordLatticeFullRank_proof_2e8df524b479
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:47.953177+00:00
-- url     : https://prove2.me/submissions/65e30b0e-675e-43f4-b2d9-be1e9303df16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordLatticeFullRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordLatticeFullRank
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField Module
noncomputable section
variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace CoordLatticeFullRank
theorem _root_.solution (v : Basis ι E W) : CoordLatticeFullRank.Statement v := by
  intro La hL
  set f : W →ₗ[E] ι → E := (v.equivFun : W →ₗ[E] ι → E) with hf
  refine ⟨?_, ?_⟩
  · classical
    obtain ⟨s, hs⟩ := hL.fg
    refine ⟨s.image f.toAddMonoidHom, ?_⟩
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hs]
  set S : Set (ι → E) := ((La.map f.toAddMonoidHom : AddSubgroup (ι → E)) : Set (ι → E)) with hS
  set T : Submodule ℚ (ι → E) := Submodule.span ℚ S with hT

  have key : ∀ (a : E), ∀ s ∈ S, a • s ∈ T := by
    intro a s hs
    obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({a} : Finset E)
    have hda : IsIntegral ℤ (d • a) := hint a (Finset.mem_singleton_self a)
    obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_map).mp hs
    let b : 𝓞 E := ⟨d • a, hda⟩
    have hbx : ((b : E) • x) ∈ La := hL.smul_mem b x hx
    have hfb : f ((b : E) • x) ∈ S := (AddSubgroup.mem_map).mpr ⟨_, hbx, rfl⟩
    have hd' : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
    have heq : a • f.toAddMonoidHom x = ((d : ℚ)⁻¹) • f ((b : E) • x) := by
      rw [map_smul]
      show a • f x = ((d : ℚ)⁻¹) • ((d • a) • f x)
      rw [zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [heq]
    exact T.smul_mem _ (Submodule.subset_span hfb)

  have stable : ∀ (a : E), ∀ y ∈ T, a • y ∈ T := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact key a s hs
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact T.add_mem hy hz
    | smul q y _ hy =>
      rw [smul_comm]
      exact T.smul_mem q hy
  let T' : Submodule E (ι → E) :=
    { carrier := T
      add_mem' := fun hy hz => T.add_mem hy hz
      zero_mem' := T.zero_mem
      smul_mem' := fun a y hy => stable a y hy }
  have hspan : Submodule.span E S = ⊤ := by
    have hSim : S = f '' (La : Set W) := by
      rw [hS, AddSubgroup.coe_map]; rfl
    rw [hSim, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact v.equivFun.surjective
  have hle : Submodule.span E S ≤ T' := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun y _ => hle (Submodule.mem_top)
end CoordLatticeFullRank
end GroundTheory.Heights₂.Heights.FiniteCovolume
