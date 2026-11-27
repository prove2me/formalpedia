-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectCovering_hypotheses_met_fbb559825cc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:59.884804+00:00
-- url     : https://prove2.me/submissions/a0c99f9f-ffa0-448f-9f1a-34ba4eb54096

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectCovering
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
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace SemidirectCovering
theorem _root_.solution : ∃ (i : C2 →* C2 × C2) (q : C2 × C2 →* C2)
    (j : C2 →* C2 × C2) (μL : Measure C2) (_ : μL.IsHaarMeasure) (μN : Measure C2)
    (_ : μN.IsHaarMeasure) (Γ : Subgroup (C2 × C2)) (C : Set C2) (T : Set C2)
    (ν : Measure (C2 × C2)) (_ : ν.IsHaarMeasure),
    Continuous i ∧ Continuous q ∧ IsClosedEmbedding j ∧ (∀ l, q (i l) = l) ∧
    (∀ g, q g = 1 ↔ g ∈ j.range) ∧
    (∀ l, μN.map (fun n => i l * j n * (i l)⁻¹) = μN.map j) ∧ IsCompact C ∧ MeasurableSet T ∧
    μL T < ⊤ ∧ (∀ n, ∃ δ, j δ ∈ Γ ∧ δ * n ∈ C) ∧ (∀ l, ∃ γ ∈ Γ, q γ * l ∈ T) ∧
    i ≠ 1 ∧ j ≠ 1 := by
  refine ⟨MonoidHom.inl C2 C2, MonoidHom.fst C2 C2, MonoidHom.inr C2 C2, Measure.haar,
    inferInstance, Measure.haar, inferInstance, ⊤, Set.univ, Set.univ, Measure.haar, inferInstance,
    continuous_of_discreteTopology, continuous_of_discreteTopology,
    continuous_of_discreteTopology.isClosedEmbedding (fun a b hab => by simpa using congrArg Prod.snd hab),
    fun l => rfl, ?_, ?_, isCompact_univ, MeasurableSet.univ, measure_lt_top _ _,
    fun n => ⟨1, Subgroup.mem_top _, by simp⟩, fun l => ⟨1, Subgroup.mem_top _, by simp⟩, ?_, ?_⟩
  · rintro ⟨a, b⟩
    constructor
    · intro hg
      refine ⟨b, ?_⟩
      simp only [MonoidHom.coe_fst] at hg
      simp [hg]
    · rintro ⟨n, hn⟩
      rw [← hn]
      simp
  · intro l
    congr 1
    funext n
    ext <;> simp
  · intro h1
    have := congrArg (fun f => (f (Multiplicative.ofAdd 1)).1) h1
    simp at this
  · intro h1
    have := congrArg (fun f => (f (Multiplicative.ofAdd 1)).2) h1
    simp at this
end SemidirectCovering
end GroundTheory.Heights₂.Heights.FiniteCovolume
