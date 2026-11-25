-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_proof_286c88a5bb3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:48:30.246411+00:00
-- url     : https://prove2.me/submissions/6e72c256-7047-410a-acb4-c17e053039f0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_posDef_exists_lower_ced1adf397bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_norm_mul_apply_le_0a1fce1ba032
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_exists_rightInv_88baf47ce09d
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
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
open scoped ComplexOrder
noncomputable section
open BoundedInverseCompact
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace BoundedInverseCompact
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) :
    BoundedInverseCompact.Statement h v := by
  intro M n e he C
  obtain ⟨c, hc⟩ := exists_rightInv v he
  choose κ hκ hκle using fun w => posDef_exists_lower (M.posDef w)
  set U : InfinitePlace E → Matrix ι (Fin n) ℂ := fun w => Matrix.of fun k a => vecAt v (e a) w k
  set R : InfinitePlace E → Matrix (Fin n) ι ℂ := fun w => Matrix.of fun a i => w.embedding (c i a)
  set H := gramAt h v
  set D : InfinitePlace E → ℝ := fun w => 1 + C ^ 2 / κ w
  set r1 : InfinitePlace E → ι → ι → ℝ := fun w _ i => ∑ a, D w * ‖R w a i‖
  set r2 : InfinitePlace E → ι → ι → ℝ :=
    fun w j i => ∑ l, (∑ k, ‖(H w)⁻¹ j k‖ * r1 w l k) * ‖H w l i‖

  have hBx : ∀ r : ι → ι → ℝ, IsCompact {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} := by
    intro r
    have : {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} =
        Set.pi Set.univ fun i => Set.pi Set.univ fun j => Metric.closedBall (0 : ℂ) (r i j) := by
      ext A
      constructor
      · intro hA i _ j _
        simpa using hA i j
      · intro hA i j
        simpa using hA i (Set.mem_univ _) j (Set.mem_univ _)
    rw [this]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  set K : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ({A | ∀ i j, ‖A i j‖ ≤ r2 w i j} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r1 w i j}))
  have hK : ∀ w, IsCompact (K w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hBx _).prod (MulOpposite.opHomeomorph.isCompact_preimage.mp (hBx _)))
  set S := {g : archUnitary h v | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  have hclosed : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_le ?_ continuous_const
    have hw : ∀ w, Continuous fun x : archUnitary h v =>
        (((x⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) := fun w =>
      Units.continuous_val.comp ((continuous_apply w).comp (continuous_subtype_val.comp continuous_inv))
    have hm : ∀ w, Continuous fun x : archUnitary h v => invApply x (vecAt v (e a)) w := fun w =>
      (hw w).matrix_mulVec continuous_const
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
      ((continuous_star.comp (hm w)).dotProduct (continuous_const.matrix_mulVec (hm w))))
  rw [Subtype.isCompact_iff]
  refine (isCompact_univ_pi hK).of_isClosed_subset
    ((isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _ hclosed) ?_
  rintro _ ⟨g, hg, rfl⟩ w -
  set Gi : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set G : Matrix ι ι ℂ := (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

  have hy : ∀ a, ‖invApply g (vecAt v (e a)) w‖ ≤ D w := by
    intro a
    set y := invApply g (vecAt v (e a))
    have hnn : ∀ w', 0 ≤ (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re := fun w' =>
      (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (y w'))).1
    have h0 := Finset.sum_nonneg fun w' (_ : w' ∈ Finset.univ) => hnn w'
    have hsum : ∑ w', (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re ≤ C ^ 2 := by
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hg a) 2
    have hterm := (Finset.single_le_sum (fun w' _ => hnn w') (Finset.mem_univ w)).trans hsum
    have hk := hκle w (y w)
    have hq : ‖y w‖ ^ 2 ≤ C ^ 2 / κ w := by
      rw [le_div_iff₀ (hκ w)]
      nlinarith
    simp only [D]
    nlinarith [norm_nonneg (y w)]

  have hGiU : ∀ j a, (Gi * U w) j a = invApply g (vecAt v (e a)) w j := by
    intro j a
    simp [Gi, U, invApply, mul_apply, mulVec, dotProduct]
  have hGi_eq : Gi = Gi * U w * R w := by
    rw [Matrix.mul_assoc, hc w, Matrix.mul_one]
  have hGi_le : ∀ j i, ‖Gi j i‖ ≤ r1 w j i := by
    intro j i
    rw [hGi_eq]
    refine (norm_mul_apply_le _ _ j i).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [hGiU]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ j).trans (hy a)) (norm_nonneg _)

  have hHdet : IsUnit (H w).det := by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  have hinv : Giᴴ * H w * Gi = H w := (mem_archUnitary.mp (g⁻¹).2) w
  have hGiG : Gi * G = 1 := by
    simp only [Gi, G, Subgroup.coe_inv, Pi.inv_apply]
    exact Units.inv_mul _
  have hG_eq : G = (H w)⁻¹ * Giᴴ * H w := by
    have h1 : Giᴴ * H w = H w * G := by
      calc Giᴴ * H w = Giᴴ * H w * (Gi * G) := by rw [hGiG, Matrix.mul_one]
        _ = H w * G := by rw [← Matrix.mul_assoc, hinv]
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHdet, Matrix.one_mul]
  have hG_le : ∀ j i, ‖G j i‖ ≤ r2 w j i := by
    intro j i
    rw [hG_eq]
    refine (norm_mul_apply_le _ _ j i).trans
      (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_apply_le _ _ j l).trans
      (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [conjTranspose_apply, norm_star]
    exact hGi_le l k
  exact ⟨hG_le, hGi_le⟩
end BoundedInverseCompact
end GroundTheory.Heights₂.Heights.FiniteCovolume
