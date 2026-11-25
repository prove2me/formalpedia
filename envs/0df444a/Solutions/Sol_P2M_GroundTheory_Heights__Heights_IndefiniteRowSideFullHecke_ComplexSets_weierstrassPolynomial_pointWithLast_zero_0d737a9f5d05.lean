-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_pointWithLast_zero_0d737a9f5d05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:23.286053+00:00
-- url     : https://prove2.me/submissions/45ad1f7b-d76e-4d8c-a934-68aece2c5539

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation

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
open Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ)
    (hc : ∀ j, c j 0 = 0) (t : ℂ) : weierstrassPolynomial c (pointWithLast 0 t) = t ^ d := by
  have h : (fun i => pointWithLast (0 : σ → ℂ) t (some i)) = 0 := rfl
  simp only [weierstrassPolynomial, h, hc, zero_mul, Finset.sum_const_zero, add_zero]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
