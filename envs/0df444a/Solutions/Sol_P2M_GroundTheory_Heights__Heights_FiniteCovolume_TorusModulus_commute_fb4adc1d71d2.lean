-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_commute_fb4adc1d71d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:55.697298+00:00
-- url     : https://prove2.me/submissions/70c7a515-239f-4d36-b6cc-474e597e9eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsRadicalTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusModulus
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
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
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace TorusModulus
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v) (a : InfinitePlace E → ℂ)
    (hgx : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      a w • vecAt v x₀ w)
    (hgw : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w =
      (starRingEnd ℂ (a w))⁻¹ • vecAt v w₀ w)
    (hgY : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (k : archUnitary h v) (hk : k ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) : g * k = k * g := by
  obtain ⟨hkx, hkw⟩ := Subgroup.mem_inf.1 hk
  apply Subtype.ext
  funext w
  apply Units.ext
  simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
  refine matrix_ext_mulVec fun z => ?_
  have hH := (h2 w).1
  have hAA : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.1, map_zero]
  have hBB : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 := by
    rw [hForm, ← h1 w, hp.2.1, map_zero]
  have hAB : hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
    rw [hForm, ← h1 w, hp.2.2, map_one]
  have hBA : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
    rw [← hForm_conj hH, hAB, map_one]
  have hKu : (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w :=
    mem_archUnitary.1 k.2 w
  set H := gramAt h v w
  set A := vecAt v x₀ w
  set B := vecAt v w₀ w
  set G := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set K := ((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  have hKA : K *ᵥ A = A := hkx w
  have hKB : K *ᵥ B = B := hkw w
  set y := z - hForm H B z • A - hForm H A z • B with hy
  have hyA : hForm H A y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hAA, hAB]
    ring
  have hyB : hForm H B y = 0 := by
    rw [hy, hForm_sub_right, hForm_sub_right, hForm_smul_right, hForm_smul_right, hBA, hBB]
    ring
  have hKyA : hForm H A (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu A y
    rw [hKA] at e
    rw [e, hyA]
  have hKyB : hForm H B (K *ᵥ y) = 0 := by
    have e := hForm_mulVec_of_unitary H hKu B y
    rw [hKB] at e
    rw [e, hyB]
  have hGy : G *ᵥ y = y := hgY w y hyA hyB
  have hGKy : G *ᵥ (K *ᵥ y) = K *ᵥ y := hgY w _ hKyA hKyB
  have hGA : G *ᵥ A = a w • A := hgx w
  have hGB : G *ᵥ B = (starRingEnd ℂ (a w))⁻¹ • B := hgw w
  have hz : z = y + hForm H B z • A + hForm H A z • B := by rw [hy]; abel
  rw [← mulVec_mulVec, ← mulVec_mulVec, hz]
  simp only [mulVec_add, mulVec_smul, hKA, hKB, hGy, hGKy, hGA, hGB]
end TorusModulus
end GroundTheory.Heights₂.Heights.FiniteCovolume
