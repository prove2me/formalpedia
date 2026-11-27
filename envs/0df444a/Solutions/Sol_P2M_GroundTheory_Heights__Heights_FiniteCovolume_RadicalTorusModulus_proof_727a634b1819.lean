-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_RadicalTorusModulus_proof_727a634b1819
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:45.375487+00:00
-- url     : https://prove2.me/submissions/1ad4dce2-cea4-4b77-9f6c-eb2e46d891ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsRadicalTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_map_eq_smul_of_coordinates_dd57324cb110
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_heisScale_529d1701378d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_placeScale_7f893252c050
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisHomeo_apply_9d3b6d544422
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_mul_543a6845588e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_torus_5ad83cf0adca
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
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace RadicalTorusModulus
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) :
    RadicalTorusModulus.Statement h v := by
  intro x₀ w₀ hp g α hga _ hgy μ _ f hf
  have : BorelSpace (unipRadical h v x₀) :=
    Subtype.borelSpace (unipRadical h v x₀ : Set (archUnitary h v))
  set φ := heisHomeo (v := v) hp with hφ
  set lam : Measure (HeisCoord h v x₀ w₀) :=
    (Measure.addHaar : Measure (heisY h v x₀ w₀)).prod volume with hlam
  set L : HeisCoord h v x₀ w₀ →ₗ[ℝ] HeisCoord h v x₀ w₀ :=
    (heisScale h v x₀ w₀ fun w => starRingEnd ℂ (α w)).prodMap
      (placeScale fun w => Complex.normSq (α w)) with hLdef
  have hα : ∀ w, α w ≠ 0 := by
    intro w h0
    obtain ⟨-, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
    have e := congrArg (fun z => ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ z)
      (hga w)
    simp only [h0, zero_smul, mulVec_zero, mulVec_mulVec, Units.inv_mul, one_mulVec] at e
    rw [e, hForm, star_zero, zero_dotProduct] at hab
    exact zero_ne_one hab
  have hdet : LinearMap.det L = ∏ w, Complex.normSq (α w) ^ (Fintype.card ι - 1) := by
    rw [hLdef, LinearMap.det_prodMap, det_heisScale hp, det_placeScale, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have := finrank_heisYAt (v := v) hp w
    rw [Complex.normSq_conj, ← pow_succ]
    congr 1
    omega
  have hpos : 0 < LinearMap.det L := by
    rw [hdet]
    exact Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 (hα w)) _
  have hLc : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  have : BorelSpace (heisY h v x₀ w₀) := Subtype.borelSpace _
  have : lam.IsAddHaarMeasure := by
    rw [hlam]
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hLm : lam.map L = ENNReal.ofReal |(LinearMap.det L)⁻¹| • lam :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar lam hpos.ne'
  have hL : ∀ n, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam := by
    intro n
    obtain ⟨p, rfl⟩ := φ.surjective n
    set f : heisY h v x₀ w₀ → InfinitePlace E → ℝ := fun y w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((y : InfinitePlace E → ι → ℂ) w)).im with hf
    have e : (fun x => φ.symm (φ p * φ x)) = fun x => (p.1 + x.1, (p.2 - f x.1) + x.2) := by
      funext x
      rw [hφ, heisHomeo_apply, heisHomeo_apply, heisPoint_mul, ← heisHomeo_apply,
        Homeomorph.symm_apply_apply]
      refine Prod.ext rfl ?_
      simp only [hf]
      abel
    rw [e]
    have hfc : Continuous f := continuous_pi fun w => Complex.continuous_im.comp
      (continuous_hForm_right _ _ ((continuous_apply w).comp continuous_subtype_val))
    refine MeasurePreserving.skew_product (f := fun y => p.1 + y)
      (g := fun y t => (p.2 - f y) + t) (measurePreserving_add_left _ p.1) ?_
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_left volume _).map_eq)
    exact ((continuous_const.sub (hfc.comp continuous_fst)).add continuous_snd).measurable
  have hmap := map_eq_smul_of_coordinates lam φ hL L hLc _ hLm μ
  have hc : ∀ n, (((φ ∘ L ∘ φ.symm) n : unipRadical h v x₀) : archUnitary h v) = g * n * g⁻¹ := by
    intro n
    conv_rhs => rw [← φ.apply_symm_apply n]
    exact (heisPoint_torus hp g α hga hgy _).symm
  have hcm : Measurable (φ ∘ L ∘ φ.symm) :=
    φ.continuous.measurable.comp (hLc.comp φ.symm.continuous.measurable)
  have hfm : Measurable fun n : unipRadical h v x₀ => f n := hf.comp measurable_subtype_coe
  have hk : ENNReal.ofReal |(LinearMap.det L)⁻¹| =
      ∏ w, ‖α w‖ₑ⁻¹ ^ (2 * (finrank E W - 1)) := by
    rw [abs_of_pos (inv_pos.2 hpos), hdet, ← Finset.prod_inv_distrib,
      ENNReal.ofReal_prod_of_nonneg fun w _ => inv_nonneg.2 (pow_nonneg (Complex.normSq_nonneg _) _),
      Module.finrank_eq_card_basis v]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hp' : 0 < ‖α w‖ := norm_pos_iff.2 (hα w)
    rw [Complex.normSq_eq_norm_sq, ← pow_mul, ← inv_pow, ENNReal.ofReal_pow (inv_nonneg.2 hp'.le),
      ENNReal.ofReal_inv_of_pos hp', ofReal_norm]
  calc ∫⁻ n, f (g * n * g⁻¹) ∂μ
      = ∫⁻ n, f (((φ ∘ L ∘ φ.symm) n : unipRadical h v x₀) : archUnitary h v) ∂μ :=
        lintegral_congr fun n => by rw [hc]
    _ = ∫⁻ n, f n ∂(μ.map (φ ∘ L ∘ φ.symm)) := (lintegral_map hfm hcm).symm
    _ = (∏ w, ‖α w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ n, f n ∂μ := by
        rw [hmap, lintegral_smul_measure, hk, smul_eq_mul]
end RadicalTorusModulus
end GroundTheory.Heights₂.Heights.FiniteCovolume
