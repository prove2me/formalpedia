-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_proof_286b4b63e536
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:55:41.515548+00:00
-- url     : https://prove2.me/submissions/8ba3b73b-4e71-448c-81d9-ab3b0bbadbbb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCoordEmbedBasis
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsZsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementArchCocompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_exists_zsmul_mem_b836dd55284f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_apply_6c33936e53d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementArchCocompact_projAt_vecAt_e2b25eee4c71
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_ComplementExtension_proof_b489f5d0bce6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CoordEmbedBasis_proof_0ebb0c03bf39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_coordEmbed_apply_57a659e1152c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAtHom_apply_5d779c7499d4
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
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open ComplementArchCocompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace ComplementArchCocompact
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) :
    ComplementArchCocompact.Statement h v := by
  classical
  intro La x₀ w₀ m hLa hp hm
  obtain ⟨hli, hdim⟩ := CoordEmbedBasis.proof E ι
  let b₀ := Pi.basis fun _ : ι => integralBasis E
  let Bs := basisOfLinearIndependentOfCardEqFinrank' _ hli
    (by rw [hdim, finrank_eq_card_basis b₀])
  let e : _ → W := fun k => v.equivFun.symm (b₀ k)
  have hBe : ∀ k, Bs k = vecAt v (e k) := by
    intro k
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    funext w i
    rw [vecAt, coordEmbed_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let p : _ → W := fun k => (ComplementExtension.proj hp (e k) : W)
  choose d hd hdL using fun k => exists_zsmul_mem hLa (p k)
  let f : _ → W := fun k => m • d k • p k
  let D : _ → ℝ := fun k => (m : ℝ) * d k
  have hD : ∀ k, D k ≠ 0 := fun k =>
    mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hd k)
  have hf : ∀ k, vecAt v (f k) = D k • vecAt v (p k) := by
    intro k
    simp only [f, D, ← vecAtHom_apply, map_nsmul, map_zsmul]
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
  refine ⟨(fun t : _ → ℝ => ∑ k, t k • vecAt v (f k)) '' Set.Icc 0 1,
    isCompact_Icc.image (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).smul continuous_const), fun Y hY => ?_⟩
  have hPY : projAt h v x₀ w₀ Y = Y := by
    funext w
    rw [projAt_apply, (hY w).1, (hY w).2, zero_smul, zero_smul, sub_zero, sub_zero]
  set s : _ → ℝ := fun k => Bs.repr Y k * (D k)⁻¹ with hs
  have hYs : Y = ∑ k, s k • vecAt v (f k) := by
    calc Y = (projAt h v x₀ w₀).restrictScalars ℝ (∑ k, Bs.repr Y k • Bs k) := by
          rw [Bs.sum_repr]; exact hPY.symm
      _ = ∑ k, Bs.repr Y k • vecAt v (p k) := by
          simp only [map_sum, map_smul, LinearMap.restrictScalars_apply, hBe]
          exact Finset.sum_congr rfl fun k _ => by rw [projAt_vecAt]
      _ = _ := Finset.sum_congr rfl fun k _ => by
          rw [hf, smul_smul, hs, mul_assoc, inv_mul_cancel₀ (hD k), mul_one]
  refine ⟨∑ k, ⌊s k⌋ • f k, ?_, ⟨∑ k, ⌊s k⌋ • d k • p k, ?_, ?_⟩,
    ⟨fun k => Int.fract (s k), ⟨fun k => Int.fract_nonneg _, fun k => (Int.fract_lt_one _).le⟩, ?_⟩⟩
  · exact Submodule.sum_mem _ fun k _ =>
      zsmul_mem (nsmul_mem (zsmul_mem (ComplementExtension.proj hp (e k)).2 _) _) _
  · exact La.sum_mem fun k _ => La.zsmul_mem (hdL k) _
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  · show ∑ k, Int.fract (s k) • vecAt v (f k) = Y - vecAt v (∑ k, ⌊s k⌋ • f k)
    conv_rhs => rw [hYs]
    rw [← vecAtHom_apply, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, vecAtHom_apply, ← Int.cast_smul_eq_zsmul ℝ, ← sub_smul, Int.self_sub_floor]
end ComplementArchCocompact
end GroundTheory.Heights₂.Heights.FiniteCovolume
