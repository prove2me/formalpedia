-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SerreNormalOfRegularDepth_proof_55313c9ea8d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:06:42.843331+00:00
-- url     : https://prove2.me/submissions/67319a81-70f1-45a3-bf16-e6bfbc193811

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isIntegrallyClosed_of_serre_8afe127d72cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isDomain_of_serre_84d7177c1de9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SerreRAt_of_ringEquiv_9a6f5f5d4ec0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SerreSAt_of_ringEquiv_fc76ab8f755f


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
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace SerreNormalOfRegularDepth
theorem _root_.solution : SerreNormalOfRegularDepth.Statement := by
  intro A _ hA hR hS P _
  set B := Localization.AtPrime P
  have hRB : SerreR B 1 := fun Q _ =>
    (hR (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  have hSB : SerreS B 2 := fun Q _ =>
    (hS (Q.comap (algebraMap A B))).of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization P.primeCompl Q).toRingEquiv
  exact ⟨isDomain_of_serre hRB hSB, isIntegrallyClosed_of_serre hRB hSB⟩
end SerreNormalOfRegularDepth
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
