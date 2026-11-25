-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isWeaklyRegular_map_ringEquiv_22dca5d63af4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:49.812059+00:00
-- url     : https://prove2.me/submissions/1899afe3-15fc-4cdc-9c69-e02a3fc6e7ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreConditions
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreSFlatAscent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatDimFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreSFlatAscent

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
open IsLocalRing RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {rs : List R}
    (h : IsWeaklyRegular R rs) : IsWeaklyRegular S (rs.map e) :=
  (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv) (List.forall₂_map_right_iff.mpr
    (List.forall₂_same.mpr fun r _ x => by simp [smul_eq_mul]))).mp h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
