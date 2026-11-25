-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_min_add_le_min_add_min_327a0a674e02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:27.108208+00:00
-- url     : https://prove2.me/submissions/b8781e02-2070-4e8f-b41d-b3c9ee3d9aeb

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
theorem _root_.solution {k a b : WithBot ℕ∞} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min k (a + b) ≤ min k a + min k b := by
  rcases le_total k a with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min hk hb))
  rcases le_total k b with h' | h'
  · rw [min_eq_left h']
    exact (min_le_left _ _).trans (le_add_of_nonneg_left (le_min hk ha))
  rw [min_eq_right h, min_eq_right h']
  exact min_le_right _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
