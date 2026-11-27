-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_proof_4ebcf02cd642
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:26.776487+00:00
-- url     : https://prove2.me/submissions/76dbb5ba-f4c3-42ee-b377-760dd260ddd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisTer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_isLocalization_coneVarMap_9d3466758b52


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.Inter
namespace regularityLocalFlat_holds
theorem _root_.solution : regularityLocalFlat_holds.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP.1
  have := hW.1
  choose v hv using hW.2.2
  have hA := regularityLocalFlat_holds.isLocalRing hPW
  have hloc := regularityLocalFlat_holds.isLocalization_coneVarMap hPW hP.2.1 hW.2.1 v hv
  let _ := (regularityLocalFlat_holds.coneVarMap P W hPW v).toRingHom.toAlgebra
  have := regularityLocalFlat_holds.isPrime_map_C K (maximalIdeal (locRing P W))
  have : IsScalarTower (locRing P W) (MvPolynomial K (locRing P W)) (coneLocRing P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((regularityLocalFlat_holds.coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocRing P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _)).primeCompl
    have : Module.Free (locRing P W) (MvPolynomial K (locRing P W)) :=
      Module.Free.of_basis (MvPolynomial.basisMonomials K (locRing P W))
    have : Module.Flat (locRing P W) (MvPolynomial K (locRing P W)) := Module.Flat.of_free
    exact Module.Flat.trans _ (MvPolynomial K (locRing P W)) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
      (coneLocRing P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
end regularityLocalFlat_holds
end GroundTheory.Heights₂.Heights.Inter
