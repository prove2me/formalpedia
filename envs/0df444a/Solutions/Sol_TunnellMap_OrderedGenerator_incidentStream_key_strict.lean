-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.incidentStream_key_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:20.7478+00:00
-- url     : https://prove2.me/submissions/06c319f3-9c3f-4046-88c5-93ef949ea8c9

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_validIndex_key_eq_orbitEdgeKey
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
import Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_key_strict
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
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
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
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
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


attribute [local simp] TunnellMap.OrderedGenerator.mem_orderedIndexList

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
set_option maxHeartbeats 800000
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : Fin (incidentStream hnpos s F).length} (hij : i < j) :
    orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F).get i) <
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((incidentStream hnpos s F).get j) := by
  let i' : Fin (orderedIndexList s F).length :=
    ⟨i.1, by simpa [incidentStream] using i.2⟩
  let j' : Fin (orderedIndexList s F).length :=
    ⟨j.1, by simpa [incidentStream] using j.2⟩
  have hij' : i' < j' := hij
  have hkey := orderedIndexList_key_strict s F hij'
  rw [validIndex_key_eq_orbitEdgeKey hnpos s F
      ((orderedIndexList s F).get i'),
    validIndex_key_eq_orbitEdgeKey hnpos s F
      ((orderedIndexList s F).get j')] at hkey
  have hiMap : (incidentStream hnpos s F).get i =
      targetOrbitOfValid hnpos s F ((orderedIndexList s F).get i') :=
    List.getElem_map (targetOrbitOfValid hnpos s F)
      (l := orderedIndexList s F) (i := i.1) (h := i.2)
  have hjMap : (incidentStream hnpos s F).get j =
      targetOrbitOfValid hnpos s F ((orderedIndexList s F).get j') :=
    List.getElem_map (targetOrbitOfValid hnpos s F)
      (l := orderedIndexList s F) (i := j.1) (h := j.2)
  exact (congrArg (orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)) hiMap).trans_lt
    (hkey.trans_eq
      (congrArg (orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)) hjMap.symm))
end TunnellMap.OrderedGenerator
