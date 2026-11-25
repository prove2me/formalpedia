-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompactHolomorphicFibreFinite_sum_normSq_sub_a47ef27fa32f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:54.984887+00:00
-- url     : https://prove2.me/submissions/a42610d3-bd9b-4600-856c-2aa2eaf2744f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNonIsolatedFibreCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCompactHolomorphicFibreFinite

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
open Topology Metric Filter
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CompactHolomorphicFibreFinite
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CompactHolomorphicFibreFinite
theorem _root_.solution {k : ℕ} (v p : Fin k → ℂ) :
    ∑ i, Complex.normSq (v i - p i) =
      ∑ i, Complex.normSq (v i) + ∑ i, Complex.normSq (p i) -
        2 * (∑ i, v i * (starRingEnd ℂ) (p i)).re := by
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_sub]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CompactHolomorphicFibreFinite
