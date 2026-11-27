-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_proof_073feb9c2335
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:45.282219+00:00
-- url     : https://prove2.me/submissions/c9269f8b-e822-436a-8d62-af38b4a4b55f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsRadicalTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusModulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_commute_fb4adc1d71d2
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684
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
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace TorusModulus
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v)
    (h3 : ComplementForm.Statement h) (h4 : StabilizerLevi.Statement h v)
    (h5 : UnipotentModulus.Statement h v) (h6 : RadicalTorusModulus.Statement h v)
    (h7 : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectHaar.Statement (archUnitary h v) (archUnitary h' v')) :
    TorusModulus.Statement h v := by
  classical
  intro x₀ w₀ hp g a hgx hgw hgY ν _ f hf
  have : FiniteDimensional E W := Module.Finite.of_basis v
  obtain ⟨h', hh'⟩ := h3 x₀ w₀ hp
  let v' := Module.finBasis E (hypComplement h x₀ w₀)
  obtain ⟨i, q, hic, hqc, hqi, hker, hiw, -⟩ := h4 x₀ w₀ hp h' hh' _ v'
  let τ : archUnitary h' v' →* archUnitary h v := (vecFixGroup h v x₀).subtype.comp i
  have hτc : Continuous τ := continuous_subtype_val.comp hic
  have hτmem : ∀ t, τ t ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀ :=
    fun t => Subgroup.mem_inf.2 ⟨(i t).2, hiw t⟩
  have hnorm : ∀ t, ∀ x ∈ unipRadical h v x₀, τ t * x * (τ t)⁻¹ ∈ unipRadical h v x₀ := by
    intro t x hx
    have hxP : x ∈ vecFixGroup h v x₀ := unipRadical_le_vecFixGroup h v x₀ hx
    have e := (hker (i t * ⟨x, hxP⟩ * (i t)⁻¹)).1 (by
      rw [map_mul, map_mul, map_inv, hqi, (hker ⟨x, hxP⟩).2 hx, mul_one, mul_inv_cancel])
    simpa [τ] using e
  have hinj : ∀ t, τ t ∈ unipRadical h v x₀ → t = 1 := by
    intro t ht
    rw [← hqi t]
    exact (hker (i t)).2 ht
  have hdec : ∀ p : vecFixGroup h v x₀, (p : archUnitary h v) * (τ (q p))⁻¹ ∈ unipRadical h v x₀ := by
    intro p
    have e := (hker (p * (i (q p))⁻¹)).1 (by rw [map_mul, map_inv, hqi, mul_inv_cancel])
    simpa [τ] using e
  let νN : Measure (unipRadical h v x₀) := Measure.haar
  let ρ : Measure (archUnitary h' v') := Measure.haar
  have hδ : ∀ (t : archUnitary h' v') (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂νN = ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x, f x ∂νN := by
    intro t f hf
    have e := h5 x₀ w₀ hp νN (τ t) (hτmem t)
    have hm : Measurable fun n : unipRadical h v x₀ => τ t * (n : archUnitary h v) * (τ t)⁻¹ :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    rw [ENNReal.coe_one, one_mul, ← lintegral_map hf hm, e, lintegral_map hf measurable_subtype_coe]
  obtain ⟨c, -, hc⟩ := h7 x₀ w₀ h' _ v' (vecFixGroup h v x₀) (unipRadical h v x₀)
    (isClosed_vecFixGroup h v x₀) (isClosed_unipRadical h v x₀) (unipRadical_le_vecFixGroup h v x₀)
    τ q (fun _ => 1) hτc hqc continuous_const (fun t => (i t).2) hnorm hinj hdec ν νN ρ hδ
  have hconj : ∀ t (n : archUnitary h v), g * (n * τ t) * g⁻¹ = g * n * g⁻¹ * τ t := by
    intro t n
    have e : τ t * g⁻¹ = g⁻¹ * τ t := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, TorusModulus.commute h v h1 h2 hp g a hgx hgw hgY _
        (hτmem t), mul_inv_cancel_right]
    calc g * (n * τ t) * g⁻¹ = g * n * (τ t * g⁻¹) := by group
      _ = g * n * (g⁻¹ * τ t) := by rw [e]
      _ = g * n * g⁻¹ * τ t := by group
  set K := ∏ w, ‖a w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))
  have hφ : Measurable fun y : archUnitary h v => f (g * y * g⁻¹) :=
    hf.comp ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have step : ∀ t, ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN =
      K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN := by
    intro t
    simp_rw [hconj t]
    exact h6 x₀ w₀ hp g a hgx hgw hgY νN (fun y => f (y * τ t))
      (hf.comp (continuous_id.mul continuous_const).measurable)
  have hmeas : Measurable fun t => ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN :=
    Measurable.lintegral_prod_right' (f := fun p : archUnitary h' v' × unipRadical h v x₀ =>
      f (p.2 * τ p.1)) (hf.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hτc.comp continuous_fst)).measurable)
  calc ∫⁻ x, f (g * x * g⁻¹) ∂ν
      = c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) *
          ∫⁻ x : unipRadical h v x₀, f (g * (x * τ t) * g⁻¹) ∂νN ∂ρ := hc _ hφ
    _ = c * ∫⁻ t, K * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ := by
        simp_rw [ENNReal.coe_one, one_mul, step]
    _ = K * (c * ∫⁻ t, ((1 : ℝ≥0) : ℝ≥0∞) * ∫⁻ x : unipRadical h v x₀, f (x * τ t) ∂νN ∂ρ) := by
        rw [lintegral_const_mul _ hmeas]
        simp only [ENNReal.coe_one, one_mul]
        ring
    _ = K * ∫⁻ x, f x ∂ν := by rw [hc f hf]
end TorusModulus
end GroundTheory.Heights₂.Heights.FiniteCovolume
