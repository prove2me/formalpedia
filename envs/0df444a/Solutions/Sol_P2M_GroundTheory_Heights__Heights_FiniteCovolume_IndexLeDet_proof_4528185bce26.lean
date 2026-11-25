-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IndexLeDet_proof_4528185bce26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:59:31.640181+00:00
-- url     : https://prove2.me/submissions/5a097385-4b69-415d-a688-cf8ad9df5ff7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIndexLeDet
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
open NumberField Module Matrix
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace IndexLeDet
theorem _root_.solution (E : Type*) [Field E] [NumberField E] : IndexLeDet.Statement E := by
  classical
  intro A hA e a T ha hT
  have hmem : ∀ i, (a i : E) ∈ A := fun i => hA ⟨a i, rfl⟩
  let b : Fin (finrank ℚ E) → A := fun i => ⟨a i, hmem i⟩
  have hb : ∀ i, b i = ∑ j, T i j • e j := by
    intro i
    apply Subtype.ext
    simp [b, hT i]

  have hdet : T.det ≠ 0 := by
    intro h0
    have h0' : ((Int.castRingHom ℚ).mapMatrix T).det = 0 := by
      rw [← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0'
    have hsum : ∑ i, v i • (a i : E) = 0 := by
      calc ∑ i, v i • (a i : E)
          = ∑ i, ∑ j, (v i * (T i j : ℚ)) • (e j : E) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hT i, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]
        _ = ∑ j, (∑ i, v i * (T i j : ℚ)) • (e j : E) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_smul]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            have := congrFun hv j
            simp only [vecMul, dotProduct, RingHom.mapMatrix_apply, map_apply, eq_intCast,
              Pi.zero_apply] at this
            rw [this, zero_smul]
    exact hv0 (funext fun i => Fintype.linearIndependent_iff.mp ha v hsum i)

  have hliE : LinearIndependent ℤ (fun i => (a i : E)) := ha.restrict_scalars' ℤ
  have hli : LinearIndependent ℤ b :=
    LinearIndependent.of_comp (A.subtype.toIntLinearMap) hliE
  have : Module.Free ℤ A := Module.Free.of_basis e
  have : Module.Finite ℤ A := Module.Finite.of_basis e
  set N := Submodule.span ℤ (Set.range b) with hN
  let bN := Basis.span hli
  have hbN : ((↑) ∘ bN : Fin (finrank ℚ E) → A) = b := funext fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hcard := Submodule.natAbs_det_basis_change e N bN
  rw [hbN] at hcard
  have hdetb : e.det b = T.det := by
    rw [Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, hb i, map_sum]
    simp [Finsupp.single_apply]
  rw [hdetb] at hcard

  have hle : N.toAddSubgroup ≤ (intSubgroup E).addSubgroupOf A := by
    have : N ≤ ((intSubgroup E).addSubgroupOf A).toIntSubmodule := by
      rw [hN, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show b i ∈ (intSubgroup E).addSubgroupOf A
      rw [AddSubgroup.mem_addSubgroupOf]
      exact ⟨a i, rfl⟩
    exact this
  have hidx : N.toAddSubgroup.index = T.det.natAbs := hcard.symm
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  have hle' : (intSubgroup E).relIndex A ≤ T.det.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hdet) hdvd
  calc ((intSubgroup E).relIndex A : ℝ) ≤ (T.det.natAbs : ℝ) := by exact_mod_cast hle'
    _ = |(T.det : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
end IndexLeDet
end GroundTheory.Heights₂.Heights.FiniteCovolume
