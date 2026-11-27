-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SerreRFlatAscent_proof_7cd3a1f495c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:59:18.620223+00:00
-- url     : https://prove2.me/submissions/1247e05e-72e9-4e4b-8edf-fef696f30158

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreRFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscentLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreRFlatAscent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isLocalRing_closedFibre_1cfedabc2710
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_flat_of_closedFibre_c27dad4184d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_map_maximalIdeal_localization_eq_110903f3d502
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ringKrullDim_eq_add_ringKrullDim_closedFibre_2bbf7e020a6c


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
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace SerreRFlatAscent
theorem _root_.solution : SerreRFlatAscent.Statement := by
  intro A B _ _ _ hA hB hflat k hRA hfib P _ hdim
  have : IsNoetherianRing A := hA
  have : IsNoetherianRing B := hB
  have : Module.Flat A B := hflat
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  have : IsLocalHom (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) :=
    Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have := isLocalRing_closedFibre (R := Localization.AtPrime (P.under A)) (S := Localization.AtPrime P)
  let e := Ideal.quotEquivOfEq (map_maximalIdeal_localization_eq (A := A) P).symm
  have hsum := ringKrullDim_eq_add_ringKrullDim_closedFibre (R := Localization.AtPrime (P.under A))
    (S := Localization.AtPrime P)
  have h0A : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime (P.under A)) :=
    ringKrullDim_nonneg_of_nontrivial
  have h0F : (0 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P ⧸
      (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hsum] at hdim
  have hAk := (le_add_of_nonneg_right h0F).trans hdim
  have hFk := (le_add_of_nonneg_left h0A).trans hdim
  have hF : IsRegularLocalRing (primeFibreLocalRing A P) :=
    hfib P (by rw [ringKrullDim_eq_of_ringEquiv e]; exact hFk)
  exact isRegularLocalRing_of_flat_of_closedFibre (hRA (P.under A) hAk) (hF.of_ringEquiv e)
end SerreRFlatAscent
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
