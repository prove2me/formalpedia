-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceLift_exists_congruence_cd72a2a113e6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:23:52.371438+00:00
-- url     : https://prove2.me/submissions/8e7f1072-196e-4075-9d66-b2931bc33fd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsNsmulMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PCongruenceLift
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
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift
theorem _root_.solution {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]
    (L : AddSubgroup V) (hL : L.FG) (d : ℕ) (hd : 0 < d) :
    ∃ K : Subgroup (MulAction.stabilizer G L), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ L, ∃ u ∈ L, d • u = (k : G) • y - y := by
  set S := MulAction.stabilizer G L
  have hS : ∀ (s : S) (y : V), y ∈ L → (s : G) • y ∈ L := fun s y hy => by
    have := AddSubgroup.smul_mem_pointwise_smul y (s : G) L hy
    rwa [MulAction.mem_stabilizer_iff.1 s.2] at this
  let f : S → L →+ L := fun s =>
    { toFun := fun y => ⟨(s : G) • (y : V), hS s y y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun y z => Subtype.ext (smul_add _ _ _) }
  set N : AddSubgroup L := (nsmulAddMonoidHom (α := L) d).range
  have hN : ∀ s, N ≤ N.comap (f s) := by
    rintro s _ ⟨u, rfl⟩
    exact ⟨f s u, by simp [map_nsmul]⟩
  let _ : MulAction S (L ⧸ N) :=
    { smul := fun s q => QuotientAddGroup.map N N (f s) (hN s) q
      one_smul := fun q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f 1) (hN 1) (y : L ⧸ N) = y
        rw [QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (one_smul G (y : V))
      mul_smul := fun s t q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f (s * t)) (hN _) (y : L ⧸ N) =
          QuotientAddGroup.map N N (f s) (hN s) (QuotientAddGroup.map N N (f t) (hN t) y)
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (mul_smul (s : G) (t : G) (y : V)) }
  have hfg : AddGroup.FG L := (AddGroup.fg_iff_addSubgroup_fg L).2 hL
  have hfin : Finite (L ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    refine QuotientAddGroup.induction_on q fun y => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨d, hd, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩
  refine ⟨(MulAction.toPermHom S (L ⧸ N)).ker, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  intro k hk y hy
  have hq := DFunLike.congr_fun (MonoidHom.mem_ker.1 hk) ((⟨y, hy⟩ : L) : L ⧸ N)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at hq
  change QuotientAddGroup.map N N (f k) (hN k) _ = _ at hq
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hq
  obtain ⟨u, hu⟩ := hq
  refine ⟨-(u : V), L.neg_mem u.2, ?_⟩
  have := congrArg Subtype.val hu
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_nsmul, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at this
  rw [smul_neg, this]
  change -(-((k : G) • y) + y) = (k : G) • y - y
  abel
end GroundTheory.Heights₂.Heights.FiniteCovolume.CongruenceLift
