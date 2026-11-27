-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_X_inl_not_mem_lineDiagonalIdeal_672d1c73c2d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:59:58.805229+00:00
-- url     : https://prove2.me/submissions/96b64d99-091f-4a93-b3f6-073e7dd2e3e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution :
    (X (Sum.inl 0) : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) ∉ lineDiagonalIdeal := by
  intro hX
  have h1 : lineDiagonalMap (X (Sum.inl 0)) = 0 := hX
  simp [lineDiagonalMap] at h1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
