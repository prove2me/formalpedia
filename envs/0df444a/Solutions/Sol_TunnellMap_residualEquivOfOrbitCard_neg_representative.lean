-- Prove2me | solution 1 for TunnellMap.residualEquivOfOrbitCard_neg_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:00.171796+00:00
-- url     : https://prove2.me/submissions/e7b72c02-e0ec-48e1-af4b-4cd44cf20bb0

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_one
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_one
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_signAct
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_canonicalRepresentative
import Theorems.Thm_TunnellMap_signActB_one
import Theorems.Thm_TunnellMap_signActB_neg_one
import Theorems.Thm_TunnellMap_signActA_one
import Theorems.Thm_TunnellMap_signActA_neg_one
import Theorems.Thm_TunnellMap_orbit_canonicalBResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_signActB
import Theorems.Thm_TunnellMap_orbit_signActA
import Theorems.Thm_TunnellMap_FreeInvolution_liftOrbitEquiv_neg_representative
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
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
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.keyLeExec_iff
attribute [local simp] TunnellMap.keyLtExec_iff
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


attribute [local simp] TunnellMap.FreeInvolution.signAct_one
attribute [local simp] TunnellMap.FreeInvolution.signAct_neg_one
attribute [local simp] TunnellMap.FreeInvolution.orbit_signAct
attribute [local simp] TunnellMap.FreeInvolution.signOf_canonicalRepresentative
attribute [local simp] TunnellMap.signActB_one
attribute [local simp] TunnellMap.signActB_neg_one
attribute [local simp] TunnellMap.signActA_one
attribute [local simp] TunnellMap.signActA_neg_one
attribute [local simp] TunnellMap.orbit_canonicalBResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalAResidualRepresentative
attribute [local simp] TunnellMap.orbit_signActB
attribute [local simp] TunnellMap.orbit_signActA

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable {n : ℤ} (hnpos : 0 < n) [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (q : (bResidualInvolution n).Orbit) :
    residualEquivOfOrbitCard hnpos hcard
        (negBResidual ((bResidualInvolution n).representative q)) =
      negAResidual
        (preferredTarget ((bResidualInvolution n).representative q)
          ((aResidualInvolution n hnpos).representative
            (residualOrbitMatching hnpos hcard q))) := by
  classical
  show (bResidualInvolution n).liftOrbitEquiv (aResidualInvolution n hnpos)
      (residualOrbitMatching hnpos hcard)
      (fun s => orbitSignEquiv hnpos s (residualOrbitMatching hnpos hcard s))
      ((bResidualInvolution n).neg
        ((bResidualInvolution n).representative q)) = _
  rw [FreeInvolution.liftOrbitEquiv_neg_representative]
  unfold orbitSignEquiv
  by_cases hlt : directionKey
      (plusVector ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q))) <
      directionKey
      (minusVector ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)))
  · rw [if_pos hlt]
    simp only [Equiv.refl_apply]
    rw [show preferredTarget ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)) =
        (aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q) by
      unfold preferredTarget; rw [if_pos hlt]]
    rfl
  · rw [if_neg hlt]
    simp only [boolFlipEquiv, Equiv.coe_fn_mk, Bool.not_true,
      if_neg (by simp : ¬ (false = true))]
    rw [show preferredTarget ((bResidualInvolution n).representative q)
        ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)) =
        negAResidual ((aResidualInvolution n hnpos).representative
          (residualOrbitMatching hnpos hcard q)) by
      unfold preferredTarget; rw [if_neg hlt]]
    rw [negAResidual_neg]
end TunnellMap
