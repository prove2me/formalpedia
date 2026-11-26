-- Prove2me | solution 1 for TunnellMap.BlockGen.blockRecordsK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:08.704575+00:00
-- url     : https://prove2.me/submissions/43198674-28e8-4bce-8da1-0dda4836cb77

import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_KernelGenerator
import Theorems.Thm_TunnellMap_BlockGen_blockIndexListK_eq
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__3405bfd3c173
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_isqrtK_eq
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
import Theorems.Thm_TunnellMap_mergeSort_eq_isortB
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_orthogonalFrameExec_z
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_reduceFrame_z
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_tripleLexLtExec_iff
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
attribute [local simp] P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
attribute [local simp] P2M_TunnellMap_reduceFrame_e__3405bfd3c173
attribute [local simp] TunnellMap.BlockGen.remainingTrace_initial
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.OrderedGenerator.mem_orderedIndexList
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.isqrtK_eq
attribute [local simp] TunnellMap.keyLeExec_iff
attribute [local simp] TunnellMap.keyLtExec_iff
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.orthogonalFrameExec_z
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.reduceFrame_z
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.tripleLexLtExec_iff
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul



set_option autoImplicit true
open TunnellMap
open OrderedGenerator
open TunnellMap.BlockGen
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}
namespace TunnellMap.BlockGen
theorem _root_.solution (hn : 0 ≤ n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {h : ℤ}
    (h1 : 1 ≤ h) (h2 : h ≤ hMax n) :
    blockRecordsK s F h = blockRecords s F h := by
  rw [blockRecordsK, blockIndexListK_eq hn, blockRecords,
    mergeSort_eq_isortB recordLe (fun a b => by
        simpa using recordLe_total a b)
      (fun a b c => recordLe_trans a b c) ?_]
  intro a ha b hb hab hba
  have hperm : ((blockIndexList n F h).filterMap (emit s F)).Perm
      (blockRecords s F h) := (List.mergeSort_perm _ _).symm
  have hne := blockRecords_pairwise_key_ne (s := s) F h1 h2
  have ha' : a ∈ blockRecords s F h := hperm.mem_iff.mp ha
  have hb' : b ∈ blockRecords s F h := hperm.mem_iff.mp hb
  have hkey : a.key = b.key := by
    simp only [recordLe, keyLeExec_iff] at hab hba
    exact le_antisymm hab hba
  by_contra hab'
  obtain ⟨i, hi, hia⟩ := (mem_blockRecords F h a).mp ha'
  obtain ⟨j, hj, hjb⟩ := (mem_blockRecords F h b).mp hb'
  have hij : i = j :=
    recordOf_injOn_valid F (mem_validIndices_of_block F h1 h2 hi.1 hi.2)
      (mem_validIndices_of_block F h1 h2 hj.1 hj.2) (by rw [← hia, ← hjb]; exact hkey)
  exact hab' (by rw [hia, hjb, hij])
end TunnellMap.BlockGen
