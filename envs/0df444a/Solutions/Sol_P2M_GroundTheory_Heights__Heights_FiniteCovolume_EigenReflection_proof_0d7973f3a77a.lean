-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_EigenReflection_proof_0d7973f3a77a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:49:45.713929+00:00
-- url     : https://prove2.me/submissions/c0d156c3-b4d4-42f1-b0d3-946ea59302d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PEigenReflection
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


section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
open scoped ComplexOrder
private lemma expand_sandwich {ι : Type*} [Fintype ι] [DecidableEq ι] (M X X' Y : Matrix ι ι ℂ) (c a b d : ℂ)
    (h1 : X' * M = a • Y) (h2 : M * X = b • Y) (h3 : X' * M * X = d • Y) :
    (1 - c • X') * M * (1 - c • X) = M + (c * c * d - c * a - c * b) • Y := by
  have e : (1 - c • X') * M * (1 - c • X) =
      M - c • (X' * M) - c • (M * X) + (c * c) • (X' * M * X) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub,
      smul_smul]
    abel
  rw [e, h3, h1, h2]
  simp only [smul_smul, sub_smul]
  abel
end GroundTheory.Heights₂.Heights.FiniteCovolume
end

set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
open scoped ComplexOrder
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace EigenReflection
theorem _root_.solution (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenReflection.Statement ι := by
  intro H P hmaj ε hε v hv hAv
  obtain ⟨hP, hH, -, hPHP⟩ := hmaj
  have hPh : Pᴴ = P := hP.isHermitian
  have hHh : Hᴴ = H := hH
  set y : ι → ℂ := P *ᵥ v with hy
  set q : ℂ := star v ⬝ᵥ (P *ᵥ v) with hqdef
  have hqpos : 0 < q := hP.dotProduct_mulVec_pos hv
  have hq0 : q ≠ 0 := hqpos.ne'
  have hqstar : star q = q := Complex.conj_eq_iff_im.mpr (Complex.pos_iff.mp hqpos).2.symm
  have hεstar : star ε = ε := by rcases hε with rfl | rfl <;> simp
  set c : ℂ := 2 / q with hc
  have hcstar : star c = c := by rw [hc, star_div₀, hqstar]; simp
  have hcq : c * q = 2 := by rw [hc]; field_simp

  have hwy : star v ᵥ* P = star y := by rw [hy, star_mulVec, hPh]
  have hyv : star y ⬝ᵥ v = q := by rw [← hwy, ← dotProduct_mulVec]

  have hHv : H *ᵥ v = ε • y := by
    have : H *ᵥ v = P *ᵥ ((H⁻¹ * P) *ᵥ v) := by rw [mulVec_mulVec, ← Matrix.mul_assoc, hPHP]
    rw [this, show (H⁻¹ * P) *ᵥ v = ε • v from hAv, mulVec_smul]
  have hvH : star v ᵥ* H = ε • star y := by
    rw [← hHh, ← star_mulVec, hHv, star_smul, hεstar]

  have hR : pReflection P v = 1 - c • vecMulVec v (star y) := by
    rw [pReflection, ← hqdef, ← hc, vecMulVec_mul, hwy]
  have hRh : (pReflection P v)ᴴ = 1 - c • vecMulVec y (star v) := by
    rw [hR, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hcstar,
      conjTranspose_vecMulVec, star_star]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * P = (1 : ℂ) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, one_smul]
    have h2 : P * vecMulVec v (star y) = (1 : ℂ) • vecMulVec y (star y) := by
      rw [mul_vecMulVec, ← hy, one_smul]
    have h3 : vecMulVec y (star v) * P * vecMulVec v (star y) = q • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hwy, vecMulVec_mul_vecMulVec, hyv, vecMulVec_smul]
    rw [expand_sandwich P _ _ _ c 1 1 q h1 h2 h3]
    have : c * c * q - c * 1 - c * 1 = 0 := by
      rw [mul_assoc, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hRh, hR]
    have h1 : vecMulVec y (star v) * H = ε • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_smul]
    have h2 : H * vecMulVec v (star y) = ε • vecMulVec y (star y) := by
      rw [mul_vecMulVec, hHv]
      ext i j
      simp [vecMulVec_apply, mul_assoc]
    have h3 : vecMulVec y (star v) * H * vecMulVec v (star y) = (ε * q) • vecMulVec y (star y) := by
      rw [vecMulVec_mul, hvH, vecMulVec_mul_vecMulVec, smul_dotProduct, hyv, vecMulVec_smul]
      rfl
    rw [expand_sandwich H _ _ _ c ε ε (ε * q) h1 h2 h3]
    have : c * c * (ε * q) - c * ε - c * ε = 0 := by
      have : c * c * (ε * q) = (c * q) * c * ε := by ring
      rw [this, hcq]; ring
    rw [this, zero_smul, add_zero]
  · rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyv]
    rw [op_smul_eq_smul, smul_smul, hcq, two_smul]; abel
  · intro u hu
    have hyu : star y ⬝ᵥ u = 0 := by rw [← hwy, ← dotProduct_mulVec, hu]
    rw [hR, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hyu]
    simp
end EigenReflection
end GroundTheory.Heights₂.Heights.FiniteCovolume
