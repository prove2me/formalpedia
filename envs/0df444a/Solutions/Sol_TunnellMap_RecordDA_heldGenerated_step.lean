-- Prove2me | solution 1 for TunnellMap.RecordDA.heldGenerated_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:03.180925+00:00
-- url     : https://prove2.me/submissions/0c7dd277-6bd1-4c66-94e2-540bf4b7df68

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_signAct
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_one
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_one
import Theorems.Thm_TunnellMap_FreeInvolution_signOf_canonicalRepresentative
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
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
import Theorems.Thm_TunnellMap_keyLeExec_iff
import Theorems.Thm_TunnellMap_keyLtExec_iff
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_canonicalBResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_signActA
import Theorems.Thm_TunnellMap_orbit_signActB
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
import Theorems.Thm_TunnellMap_signActA_neg_one
import Theorems.Thm_TunnellMap_signActA_one
import Theorems.Thm_TunnellMap_signActB_neg_one
import Theorems.Thm_TunnellMap_signActB_one
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
attribute [local simp] TunnellMap.BlockGen.remainingTrace_initial
attribute [local simp] TunnellMap.FreeInvolution.orbit_signAct
attribute [local simp] TunnellMap.FreeInvolution.signAct_neg_one
attribute [local simp] TunnellMap.FreeInvolution.signAct_one
attribute [local simp] TunnellMap.FreeInvolution.signOf_canonicalRepresentative
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
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
attribute [local simp] TunnellMap.keyLeExec_iff
attribute [local simp] TunnellMap.keyLtExec_iff
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.orbit_canonicalAResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalBResidualRepresentative
attribute [local simp] TunnellMap.orbit_signActA
attribute [local simp] TunnellMap.orbit_signActB
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
attribute [local simp] TunnellMap.signActA_neg_one
attribute [local simp] TunnellMap.signActA_one
attribute [local simp] TunnellMap.signActB_neg_one
attribute [local simp] TunnellMap.signActB_one
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
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
omit [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hnpos : 0 < n) (frames : FrameFamily n)
    {E E' : DARun n} (hSim : Sim hnpos frames E)
    (hHG : HeldGenerated frames E) (h : step frames E = some E') :
    HeldGenerated frames E' := by
  by_cases hq0 : E.queue = []
  · rw [step_nil hq0] at h; exact absurd h (by simp)
  obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
  by_cases hs : s ∈ E.sources
  · rcases hadv : BlockGen.advance s (frames s) (E.gen s) with _ | ⟨r, g⟩
    · rw [step_exhausted hq hs hadv] at h; exact absurd h (by simp)
    · have hrmem : r ∈ fullTrace s (frames s) := by
        have hcons : remainingTrace s (frames s) (E.gen s) =
            r :: remainingTrace s (frames s) g := advance_eq_some _ hadv
        have hmem : r ∈ remainingTrace s (frames s) (E.gen s) := by
          rw [hcons]; exact List.mem_cons_self
        exact (hSim.suffix s).subset hmem
      have hupd : ∀ E'' : DARun n,
          E''.held = Function.update E.held r.target (some (s, r)) →
          HeldGenerated frames E'' := by
        intro E'' hE'' v s' r' hv
        rw [hE''] at hv
        by_cases hvr : v = r.target
        · subst hvr
          rw [Function.update_self] at hv
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact hrmem
        · rw [Function.update_of_ne hvr] at hv
          exact hHG v s' r' hv
      rcases hheld : E.held r.target with _ | ⟨old, rold⟩
      · rw [step_accept hq hs hadv hheld] at h
        obtain rfl := Option.some.inj h
        exact hupd _ rfl
      · by_cases hlt : r.key < rold.key
        · rw [step_replace hq hs hadv hheld hlt] at h
          obtain rfl := Option.some.inj h
          exact hupd _ rfl
        · rw [step_reject hq hs hadv hheld hlt] at h
          obtain rfl := Option.some.inj h
          exact hHG
  · rw [step_not_source hq hs] at h; exact absurd h (by simp)
end TunnellMap.RecordDA
