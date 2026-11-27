-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeLocalFlat_proof_8b24a34bf955
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:05.253274+00:00
-- url     : https://prove2.me/submissions/ae907268-3eb3-4d28-a586-840471be8f17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConePolyLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConeLocalFlat

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
namespace ConeLocalFlat
theorem _root_.solution (h : ConePolyLocalization.Statement.{u}) : ConeLocalFlat.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose v hv using hW.relevant
  obtain ⟨hA, hloc⟩ := h F K ι P hP W hW hPW v hv
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have : IsScalarTower (degZeroLoc P {W}) (MvPolynomial K (degZeroLoc P {W})) (coneLocal P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocal P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl
    exact Module.Flat.trans _ (MvPolynomial K (degZeroLoc P {W})) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
      (coneLocal P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
end ConeLocalFlat
end GroundTheory.Heights₂.Heights.FieldNumbers
