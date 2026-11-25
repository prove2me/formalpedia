-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedGenerators_proof_05a02d77ca4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:30.15084+00:00
-- url     : https://prove2.me/submissions/9ac1beba-ab93-4535-8f6d-ab60d85035aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StMajorantTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedGenerators
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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archLattice_84196e4f1569
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace BoundedGenerators
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : BoundedGenerators.Statement h v := by
  intro M D t ht
  obtain ⟨c, hc⟩ := hA D
  obtain ⟨d, κ, hκ⟩ := hT M
  obtain ⟨C, hC⟩ := hR d t (|κ| * c) ht
  refine ⟨d, C, fun La g hLa hmin => ?_⟩
  obtain ⟨_, _, hcov⟩ := hc La hLa
  obtain ⟨T, hTn, hTc⟩ := hκ g

  let Φ : W →+ EuclideanSpace ℝ (Fin d) :=
    ((T : (InfinitePlace E → ι → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin d)) : _ →ₗ[ℝ] _).toAddMonoidHom.comp
      (vecAtHom v)
  have hΦ : ∀ x, Φ x = T (vecAt v x) := fun x => rfl
  have hvec : Function.Injective (vecAt v) := by
    intro x y hxy
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    apply v.repr.injective
    ext i
    exact w.embedding.injective (congrFun (congrFun hxy w) i)
  have hΦinj : Function.Injective Φ := T.injective.comp hvec
  let L := ZLattice.comap ℝ (archLattice v La) T.symm.toLinearMap
  have hmemL : ∀ z, z ∈ L ↔ ∃ x ∈ La, Φ x = z := by
    intro z
    rw [← SetLike.mem_coe, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe, mem_archLattice]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [hΦ]
    constructor
    · intro hx; rw [hx]; simp
    · intro hx; rw [← hx]; simp
  have hLmin : ∀ z ∈ L, z ≠ 0 → t ≤ ‖z‖ := by
    intro z hz hz0
    obtain ⟨x, hx, rfl⟩ := (hmemL z).1 hz
    have hx0 : x ≠ 0 := by rintro rfl; exact hz0 (map_zero Φ)
    rw [hΦ, hTn]
    exact hmin x hx hx0
  have hLcov : ZLattice.covolume L ≤ |κ| * c := by
    rw [hTc]
    have h0 : 0 ≤ ZLattice.covolume (archLattice v La) := ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_right (le_abs_self κ) h0).trans
      (mul_le_mul_of_nonneg_left hcov (abs_nonneg κ))
  obtain ⟨b, hb⟩ := hC L hLmin hLcov
  choose e he heb using fun i => (hmemL (b i)).1 (b i).2
  refine ⟨e, le_antisymm ((AddSubgroup.closure_le La).2 (Set.range_subset_iff.2 he)) ?_,
    fun i => ?_⟩
  · intro x hx
    have hxL : Φ x ∈ L := (hmemL _).2 ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨Φ x, hxL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨Φ x, hxL⟩
    have hx' : x = ∑ i, r i • e i := by
      apply hΦinj
      rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, heb i]
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [← hTn, ← hΦ, heb i]
    exact hb i
end BoundedGenerators
end GroundTheory.Heights₂.Heights.FiniteCovolume
