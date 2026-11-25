-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_sum_re_embedding_cacaade79f36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:24:54.801239+00:00
-- url     : https://prove2.me/submissions/044d4e80-1b57-481f-b3a5-7bb7e6933602

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_add_conj
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
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Theta
namespace UnitaryReduction
namespace DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
section NumberFieldFacts
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
open Classical
private theorem filter_mk_eq (w : InfinitePlace E) :
    (Finset.univ.filter fun φ : E →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk φ := by rw [mk_embedding, h]
    rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  · rintro (h | h)
    · rw [h, mk_embedding]
    · rw [h, mk_conjugate_eq, mk_embedding]
private theorem embedding_ne_conjugate (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hr : InfinitePlace.IsReal w := InfinitePlace.isReal_iff.mpr
    (ComplexEmbedding.isReal_iff.mpr h.symm)
  exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) hr
end NumberFieldFacts
section DualLattice
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
end DualLattice
section DualBasis
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end DualBasis
section DualBasis2
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
end DualBasis2
section Fibres
variable {E : Type} [Field E] [NumberField E]
variable (S : MetSpace E) (τ : InfinitePlace E)
end Fibres
section Adjoints
variable {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
end Adjoints
section IdealMaps
variable {E : Type} [Field E] [NumberField E]
variable {V V' : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']
end IdealMaps
section FibMaps
variable {E : Type} [Field E] [NumberField E]
end FibMaps
end DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace DualHomPf
open scoped InnerProductSpace nonZeroDivisors
end UnitaryReduction
end GroundTheory.Heights₂.Theta
end
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
open Classical
namespace GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
theorem _root_.solution (t : E) :
    ∑ τ : InfinitePlace E, (τ.embedding t).re = (Algebra.trace ℚ E t : ℝ) / 2 := by
  have h1 : (algebraMap ℚ ℂ (Algebra.trace ℚ E t)) = ∑ σ : E →ₐ[ℚ] ℂ, σ t :=
    trace_eq_sum_embeddings (E := ℂ)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ t = ∑ φ : E →+* ℂ, φ t :=
    (Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ) (fun σ => σ t)).symm
  have h3 : ∑ φ : E →+* ℂ, φ t =
      ∑ w : InfinitePlace E, ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
        φ t :=
    (Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ) (fun φ => φ t)).symm
  have h4 : ∀ w : InfinitePlace E,
      ∑ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w), φ t =
        ((2 * (w.embedding t).re : ℝ) : ℂ) := by
    intro w
    rw [filter_mk_eq, Finset.sum_pair (embedding_ne_conjugate w), ComplexEmbedding.conjugate_coe_eq,
      Complex.add_conj]
  have h5 : ((Algebra.trace ℚ E t : ℝ) : ℂ) =
      ((∑ w : InfinitePlace E, 2 * (w.embedding t).re : ℝ) : ℂ) := by
    rw [show ((Algebra.trace ℚ E t : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E t) by simp,
      h1, h2, h3]
    push_cast
    exact Finset.sum_congr rfl fun w _ => by rw [h4 w]; push_cast; ring
  have h6 := Complex.ofReal_injective h5
  rw [h6, ← Finset.mul_sum]; ring
end GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
