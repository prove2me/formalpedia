-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_isometry_75ed28d45147
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:24.710818+00:00
-- url     : https://prove2.me/submissions/fb143b63-264c-43eb-b802-416eca5d984d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_exists_conjTranspose_mul_self_056b80eec094
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantTransport_norm_sq_sqrtMap_4722b2f5bbc1
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
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
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped MatrixOrder ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v) :
    ∃ (d : ℕ) (S : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d)),
      ∀ y, ‖S y‖ = M.len y := by
  choose Q hQ using fun w => exists_conjTranspose_mul_self (M.posDef w)
  have hnorm : ∀ y, ‖sqrtMap Q y‖ = M.len y := by
    intro y
    rw [Majorant.len, ← Real.sqrt_sq (norm_nonneg (sqrtMap Q y)), norm_sq_sqrtMap]
    simp only [hQ]
  have hinj : Function.Injective (sqrtMap Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re = 0 := by
      have := norm_sq_sqrtMap Q y
      simp only [hQ, hy, norm_zero] at this
      linarith
    have hnn : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
      (Complex.nonneg_iff.mp ((M.posDef w).posSemidef.dotProduct_mulVec_nonneg (y w))).1
    funext w
    by_contra hw
    have hpos := (Complex.lt_def.mp ((M.posDef w).dotProduct_mulVec_pos hw)).1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hnn w).mp h0 w (Finset.mem_univ _)
    simp only [Complex.zero_re] at hpos
    linarith
  have hdim : finrank ℂ (InfinitePlace E → ι → ℂ) =
      finrank ℂ (EuclideanSpace ℂ (InfinitePlace E × ι)) := by
    simp [Module.finrank_pi_fintype, finrank_euclideanSpace, Fintype.card_prod]
  let e : (InfinitePlace E → ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) :=
    LinearEquiv.ofBijective (sqrtMap Q)
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℂ (InfinitePlace E × ι))
  refine ⟨_, (e.restrictScalars ℝ).toContinuousLinearEquiv.trans b.repr.toContinuousLinearEquiv,
    fun y => ?_⟩
  simp only [ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map]
  exact hnorm y
end GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantTransport
