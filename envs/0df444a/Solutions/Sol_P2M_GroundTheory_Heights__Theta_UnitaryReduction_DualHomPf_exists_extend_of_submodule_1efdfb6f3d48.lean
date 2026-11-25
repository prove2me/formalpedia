-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_exists_extend_of_submodule_1efdfb6f3d48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:33.657661+00:00
-- url     : https://prove2.me/submissions/fa39801c-a6a9-4028-a247-11896a21e745

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
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
theorem _root_.solution (A : Submodule (𝓞 E) V) (s : A →ₗ[𝓞 E] 𝓞 E) :
    ∃ σ : V →ₗ[E] E, ∀ x : A, σ (x : V) = ((s x : 𝓞 E) : E) := by
  classical
  obtain ⟨bs, hbA, _hspan, hli⟩ := exists_linearIndependent E (A : Set V)
  let bb := Basis.span hli
  let σ₀ := bb.constr E (fun i : bs => ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E))
  obtain ⟨σ, hσ⟩ := LinearMap.exists_extend σ₀
  have hrange : Set.range ((↑) : bs → V) = bs := Subtype.range_coe
  have hσb : ∀ i : bs, σ (i : V) = ((s ⟨i.1, hbA i.2⟩ : 𝓞 E) : E) := by
    intro i
    have hi : (i : V) ∈ Submodule.span E (Set.range ((↑) : bs → V)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 : σ (i : V) = σ₀ ⟨i, hi⟩ := by
      rw [← hσ]; rfl
    have h2 : (⟨i, hi⟩ : Submodule.span E (Set.range ((↑) : bs → V))) = bb i := by
      ext; rw [Basis.span_apply]
    rw [h1, h2, Basis.constr_basis]

  have hP : ∀ y ∈ Submodule.span (𝓞 E) (bs : Set V), ∀ hy : y ∈ A,
      σ y = ((s ⟨y, hy⟩ : 𝓞 E) : E) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => intro hxA; exact hσb ⟨x, hx⟩
    | zero => intro h0; simp [show (⟨0, h0⟩ : A) = 0 from rfl]
    | add x y hx hy ihx ihy =>
      intro hxyA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have hyA : y ∈ A := Submodule.span_le.mpr hbA hy
      rw [map_add, ihx hxA, ihy hyA, show (⟨x + y, hxyA⟩ : A) = ⟨x, hxA⟩ + ⟨y, hyA⟩ from rfl,
        map_add]
      push_cast; rfl
    | smul c x hx ihx =>
      intro hcxA
      have hxA : x ∈ A := Submodule.span_le.mpr hbA hx
      have e1 : σ (c • x) = (c : E) * σ x := by
        rw [← algebraMap_smul E c x, LinearMap.map_smul, smul_eq_mul,
          RingOfIntegers.coe_eq_algebraMap]
      have e2 : s ⟨c • x, hcxA⟩ = c * s ⟨x, hxA⟩ := by
        rw [show (⟨c • x, hcxA⟩ : A) = c • ⟨x, hxA⟩ from rfl, LinearMap.map_smul, smul_eq_mul]
      rw [e1, e2, ihx hxA]
      simp
  refine ⟨σ, fun x => ?_⟩
  have hx : (x : V) ∈ Submodule.span E (bs : Set V) := by
    rw [_hspan]; exact Submodule.subset_span x.2
  obtain ⟨m, c, v, hv, hxv⟩ : ∃ (m : ℕ) (c : Fin m → E) (v : Fin m → V), (∀ i, v i ∈ bs) ∧
      (x : V) = ∑ i, c i • v i := by
    obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').mp hx
    exact ⟨m, c, fun i => (g i : V), fun i => (g i).2, hg.symm⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ Finset.univ c
  choose o ho using fun i => hd i (Finset.mem_univ i)
  have hdx : ((d : 𝓞 E) : E) • (x : V) = ∑ i, o i • v i := by
    rw [hxv, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (o i) (v i), ho i, Algebra.smul_def, mul_smul,
      RingOfIntegers.coe_eq_algebraMap]
  have hyP : ∑ i, o i • v i ∈ Submodule.span (𝓞 E) (bs : Set V) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hv i))
  have hyA : ∑ i, o i • v i ∈ A := Submodule.span_le.mpr hbA hyP
  have key := hP _ hyP hyA
  have hyeq : (⟨∑ i, o i • v i, hyA⟩ : A) = (d : 𝓞 E) • x := by
    apply Subtype.ext
    change (∑ i, o i • v i) = (d : 𝓞 E) • (x : V)
    rw [← hdx, ← algebraMap_smul E (d : 𝓞 E) (x : V), RingOfIntegers.coe_eq_algebraMap]
  rw [hyeq, map_smul, smul_eq_mul, ← hdx, map_smul, smul_eq_mul] at key
  have hd0 : ((d : 𝓞 E) : E) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d (by exact_mod_cast h)
  push_cast at key
  exact mul_left_cancel₀ hd0 key
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
