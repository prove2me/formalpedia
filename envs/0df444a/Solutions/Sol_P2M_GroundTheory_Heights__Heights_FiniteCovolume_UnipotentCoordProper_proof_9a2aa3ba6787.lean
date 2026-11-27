-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_proof_9a2aa3ba6787
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:33.827467+00:00
-- url     : https://prove2.me/submissions/8187ed2e-9db4-4e8d-911f-979790960383

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentCoordProper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_continuous_unipMat_02a32f924075
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnipotentCoordProper_eq_unipMat_8f17e87357aa
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_isUnit_det_gram
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_unipCoord_2bb02502c78f
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
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
open UnipotentCoordProper
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace UnipotentCoordProper
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentCoordProper.Statement h v := by
  intro x₀ w₀ hp K hK
  have hherm := HermAtPlace.proof h v
  set H := gramAt h v
  set X := vecAt v x₀
  set W0 := vecAt v w₀
  have hXW : ∀ w, star (X w) ⬝ᵥ (H w *ᵥ W0 w) = 1 := fun w => by
    rw [← hherm, hp.2.2, map_one]
  have hWX : ∀ w, star (W0 w) ⬝ᵥ (H w *ᵥ X w) = 1 := fun w => by
    rw [← hherm, ← h.conj_toSesq, hp.2.2, map_one, map_one]
  have hHdet : ∀ w, IsUnit (H w).det := fun w => by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  set Φ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w => unipMat (H w) (X w) (W0 w)
  set Ψ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w u => (H w)⁻¹ * (Φ w u)ᴴ * H w
  have hΦc : ∀ w, Continuous (Φ w) := fun w => continuous_unipMat _ _ _
  have hΨc : ∀ w, Continuous (Ψ w) := fun w =>
    (continuous_const.matrix_mul (hΦc w).matrix_conjTranspose).matrix_mul continuous_const
  have key : ∀ (n : unipRadical h v x₀) (w : InfinitePlace E),
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
        Φ w (unipCoord h v x₀ w₀ n w) ∧
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) =
        Ψ w (unipCoord h v x₀ w₀ n w) := by
    intro n w
    set G : Matrix ι ι ℂ := (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    have hU : Gᴴ * H w * G = H w := (mem_archUnitary.mp (n : archUnitary h v).2) w
    have hG : G = Φ w (unipCoord h v x₀ w₀ n w) :=
      eq_unipMat hU ((n.2 w).1) ((n.2 w).2) (hXW w) (hWX w)
    refine ⟨hG, ?_⟩
    set Gi : Matrix ι ι ℂ :=
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)
    have hGGi : G * Gi = 1 := Units.mul_inv _
    show Gi = (H w)⁻¹ * (Φ w (unipCoord h v x₀ w₀ n w))ᴴ * H w
    rw [← hG]
    calc Gi = (H w)⁻¹ * (Gᴴ * H w * G) * Gi := by
          rw [hU, Matrix.nonsing_inv_mul _ (hHdet w), Matrix.one_mul]
      _ = (H w)⁻¹ * Gᴴ * H w * (G * Gi) := by simp only [Matrix.mul_assoc]
      _ = (H w)⁻¹ * Gᴴ * H w := by rw [hGGi, Matrix.mul_one]
  set Kw : InfinitePlace E → Set (ι → ℂ) := fun w => (fun y => y w) '' K
  have hKw : ∀ w, IsCompact (Kw w) := fun w => hK.image (continuous_apply w)
  set C : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ((Φ w '' Kw w) ×ˢ (MulOpposite.unop ⁻¹' (Ψ w '' Kw w)))
  have hC : ∀ w, IsCompact (C w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (((hKw w).image (hΦc w)).prod
        (MulOpposite.opHomeomorph.isCompact_preimage.mp ((hKw w).image (hΨc w))))
  have hS : IsClosed {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K} :=
    hK.isClosed.preimage (continuous_unipCoord h v x₀ w₀)
  rw [Subtype.isCompact_iff, Subtype.isCompact_iff, Set.image_image]
  refine (isCompact_univ_pi hC).of_isClosed_subset ?_ ?_
  · rw [← Set.image_image]
    exact (isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _
      ((isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.isClosedMap _ hS)
  · rintro _ ⟨n, hn, rfl⟩ w -
    exact ⟨⟨_, ⟨_, hn, rfl⟩, (key n w).1.symm⟩, ⟨_, ⟨_, hn, rfl⟩, (key n w).2.symm⟩⟩
end UnipotentCoordProper
end GroundTheory.Heights₂.Heights.FiniteCovolume
