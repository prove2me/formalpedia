-- Prove2me | solution 1 for TunnellMap.RecordDA.stepTrace_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:09.525153+00:00
-- url     : https://prove2.me/submissions/a0043259-1a52-4dd0-b491-4e5158521496

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
import Theorems.Thm_P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
import Theorems.Thm_P2M_TunnellMap_reduceFrame_e__3405bfd3c173
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
import Theorems.Thm_TunnellMap_RecordDA_framesExec_apply
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
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_orbit_canonicalAResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_canonicalBResidualRepresentative
import Theorems.Thm_TunnellMap_orbit_signActA
import Theorems.Thm_TunnellMap_orbit_signActB
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
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__5f3ec14b19af
attribute [local simp] P2M_TunnellMap_orthogonalFrameExec_e__63bfe0839bbf
attribute [local simp] P2M_TunnellMap_reduceFrame_e__0c16366f5bcb
attribute [local simp] P2M_TunnellMap_reduceFrame_e__3405bfd3c173
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
attribute [local simp] TunnellMap.RecordDA.framesExec_apply
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
attribute [local simp] TunnellMap.orbit_canonicalAResidualRepresentative
attribute [local simp] TunnellMap.orbit_canonicalBResidualRepresentative
attribute [local simp] TunnellMap.orbit_signActA
attribute [local simp] TunnellMap.orbit_signActB
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
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) {E : DARun n} {ev : DAEvent n}
    {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ∃ (s : BResidual n) (rest : List (BResidual n)) (g : GenState),
      E.queue = s :: rest ∧ s ∈ E.sources ∧
      BlockGen.advanceK s (frames s) (E.gen s) =
        some (⟨ev.key, ev.target, ev.sign⟩, g) ∧
      ev.proposer = s ∧ E'.gen = Function.update E.gen s g ∧
      (ev.outcome = DAOutcome.accept ↔ E.held ev.target = none) := by
  by_cases hq0 : E.queue = []
  · rw [stepTrace, hq0] at h; exact absurd h (by simp)
  obtain ⟨s, rest, hq⟩ := List.exists_cons_of_ne_nil hq0
  by_cases hs : s ∈ E.sources
  · cases hadv : BlockGen.advanceK s (frames s) (E.gen s) with
    | none => rw [stepTrace, hq] at h; simp only [hs, if_true, hadv] at h
              exact absurd h (by simp)
    | some rg =>
        obtain ⟨r, g⟩ := rg
        cases hheld : E.held r.target with
        | none =>
            rw [stepTrace, hq] at h
            simp only [hs, if_true, hadv, hheld] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
            exact ⟨s, rest, g, hq, hs, hadv, rfl, rfl, by simp [hheld]⟩
        | some p =>
            obtain ⟨o, ro⟩ := p
            by_cases hlt : r.key < ro.key
            · rw [stepTrace, hq] at h
              simp only [hs, hadv, hheld, hlt, if_pos] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              refine ⟨s, rest, g, hq, hs, hadv, rfl, rfl, ?_⟩
              simp [hheld]
            · rw [stepTrace, hq] at h
              simp only [hs, if_true, hadv, hheld, hlt, if_false] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              refine ⟨s, rest, g, hq, hs, hadv, rfl, rfl, ?_⟩
              simp [hheld]
  · rw [stepTrace, hq] at h
    simp only [hs, if_false] at h
    exact absurd h (by simp)
end TunnellMap.RecordDA
