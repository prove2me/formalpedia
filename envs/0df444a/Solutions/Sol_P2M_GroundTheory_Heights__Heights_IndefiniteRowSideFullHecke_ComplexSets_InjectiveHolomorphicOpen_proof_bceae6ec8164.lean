-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicOpen_proof_bceae6ec8164
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:31.615822+00:00
-- url     : https://prove2.me/submissions/fcdf375b-a1b4-48d6-a0e4-f90b001c9f93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicOpen
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicOpen_finrank_eq_944780630f9b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen
theorem _root_.solution (hID : InvarianceOfDomain.Statement) : InjectiveHolomorphicOpen.Statement := by
  intro k U f hU hf hinj
  let e : (Fin k → ℂ) ≃L[ℝ] (Fin (2 * k) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (finrank_eq k)
  have hU' : IsOpen (e '' U) := e.toHomeomorph.isOpenMap U hU
  have hcont : ContinuousOn (fun y => e (f (e.symm y))) (e '' U) := by
    refine e.continuous.comp_continuousOn (hf.continuousOn.comp e.symm.continuous.continuousOn ?_)
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  have hinj' : Set.InjOn (fun y => e (f (e.symm y))) (e '' U) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ h
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h
    rw [hinj hx hx' (e.injective h)]
  have himage : (fun y => e (f (e.symm y))) '' (e '' U) = e '' (f '' U) := by
    rw [Set.image_image, Set.image_image]
    simp
  have hopen := hID (2 * k) (e '' U) (fun y => e (f (e.symm y))) hU' hcont hinj'
  rw [himage] at hopen
  have hpre : e ⁻¹' (e '' (f '' U)) = f '' U := Set.preimage_image_eq _ e.injective
  rw [← hpre]
  exact hopen.preimage e.continuous
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicOpen
