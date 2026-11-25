-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_dualBasis_51edd028661f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:07.54827+00:00
-- url     : https://prove2.me/submissions/b1069cee-f212-49d2-b58f-edaf8b0d1637

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_extend_of_submodule_1efdfb6f3d48
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
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
theorem _root_.solution (A : Submodule (𝓞 E) V) (hA : A.FG) :
    ∃ (n : ℕ) (a : Fin n → V) (σ : Fin n → (V →ₗ[E] E)),
      (∀ i, a i ∈ A) ∧ (∀ i, ∀ x ∈ A, σ i x ∈ Set.range (algebraMap (𝓞 E) E)) ∧
      ∀ x ∈ espan A, x = ∑ i, σ i x • a i := by
  classical
  have : Module.Finite (𝓞 E) A := Module.Finite.iff_fg.mpr hA
  have : Module.Flat (𝓞 E) A := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have h1 : ((a : 𝓞 E) : E) • (x : V) = 0 := by
      rw [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
      exact congrArg Subtype.val ha
    have ha0 : ((a : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero a (by exact_mod_cast h)
    rw [Submodule.mem_bot]
    exact Subtype.ext ((smul_eq_zero.mp h1).resolve_left ha0)
  have : Module.FinitePresentation (𝓞 E) A := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) A := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) A
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose σ hσ using fun i : Fin n => exists_extend_of_submodule A ((LinearMap.proj i).comp h)
  have hxA : ∀ x : A, (x : V) = ∑ i, σ i x • (f (Pi.single i 1) : V) := by
    intro x
    have h1 : x = f (h x) := (LinearMap.congr_fun hh x).symm
    have h2 : h x = ∑ i, h x i • (Pi.single i 1 : Fin n → 𝓞 E) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [h1, h2]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.coe_smul, hσ i x, ← algebraMap_smul E (h x i),
      RingOfIntegers.coe_eq_algebraMap]
    rfl
  refine ⟨n, fun i => (f (Pi.single i 1) : V), σ, fun i => (f (Pi.single i 1)).2, ?_, ?_⟩
  · intro i x hx
    exact ⟨h ⟨x, hx⟩ i, by rw [hσ i ⟨x, hx⟩, RingOfIntegers.coe_eq_algebraMap]; rfl⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hxA ⟨y, hy⟩
    | zero => simp
    | add y z _ _ hy hz =>
      conv_lhs => rw [hy, hz]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_smul]
    | smul c y _ hy =>
      conv_lhs => rw [hy]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_smul]
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
