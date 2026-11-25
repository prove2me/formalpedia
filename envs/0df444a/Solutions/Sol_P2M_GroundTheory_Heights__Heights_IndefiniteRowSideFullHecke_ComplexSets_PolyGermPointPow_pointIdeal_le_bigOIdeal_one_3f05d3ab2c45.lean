-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyGermPointPow_pointIdeal_le_bigOIdeal_one_3f05d3ab2c45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:57.395313+00:00
-- url     : https://prove2.me/submissions/5ebbc27b-1ca7-470d-8868-c2f3c070aa2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyGermPointPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyGermPointPow

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
open MvPolynomial Topology Filter Asymptotics
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
variable {σ : Type} [Fintype σ] (w : σ → ℂ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
theorem _root_.solution : holGermPointIdeal w ≤ bigOIdeal w 1 := by
  intro φ hφ
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have h0 : f w = 0 := by
    have : (Germ.valueRingHom (x := w)) (f : Germ (𝓝 w) ℂ) = 0 := by rw [hfφ]; exact hφ
    exact this
  refine ⟨f, hfφ, ?_⟩
  have := hf.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [h0, sub_zero] at this
  simpa using this.norm_right
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolyGermPointPow
