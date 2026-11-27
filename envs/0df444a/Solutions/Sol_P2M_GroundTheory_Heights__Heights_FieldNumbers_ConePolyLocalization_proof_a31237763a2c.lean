-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ConePolyLocalization_proof_a31237763a2c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:14.916933+00:00
-- url     : https://prove2.me/submissions/dac20da2-8a57-4bbe-90c9-c2674df6493d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarSurj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConePolyLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ConePolyLocalization
theorem _root_.solution (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  have hA : IsLocalRing (degZeroLoc P {W}) := h₀ F K ι P hP W hW hPW
  refine ⟨hA, ?_⟩
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}),
      q ∈ ((maximalIdeal (degZeroLoc P {W})).map
        (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e) := by
    intro q
    rw [Ideal.mem_primeCompl_iff, mem_map_C_iff]
    push Not
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨e, he⟩ := (hQ y).mp y.2
    exact h₁ F K ι P hP W hW hPW v hv y e he
  · obtain ⟨p, q, e, he, hz⟩ := h₂ F K ι P hP W hW hPW v hv z
    exact ⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩
  · refine ⟨1, ?_⟩
    rw [h₃ F K ι P hP W hW hPW v hv hxy]
end ConePolyLocalization
end GroundTheory.Heights₂.Heights.FieldNumbers
