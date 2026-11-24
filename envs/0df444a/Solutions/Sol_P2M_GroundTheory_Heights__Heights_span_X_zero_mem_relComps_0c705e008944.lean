-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_span_X_zero_mem_relComps_0c705e008944
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:57.246803+00:00
-- url     : https://prove2.me/submissions/04dc05bd-ea69-4515-9d1c-d0c5ac3473c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (F : Type*) [Field F] :
    Ideal.span {X 0} ∈ relComps ((⊥ : Ideal (MvPolynomial (Fin 2) F)) ⊔
      Ideal.span {linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0)}) := by
  have hl : linForm (fun j : Fin 2 => if j = 0 then (1 : F) else 0) = X 0 := by
    simp [linForm]
  rw [hl, bot_sup_eq]
  have : (Ideal.span {(X 0 : MvPolynomial (Fin 2) F)}).IsPrime :=
    (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  refine ⟨by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl, 1, ?_⟩
  rw [Ideal.mem_span_singleton]
  intro h
  have := (X_dvd_X (R := F)).mp h
  exact absurd this (by decide)
end GroundTheory.Heights₂.Heights
