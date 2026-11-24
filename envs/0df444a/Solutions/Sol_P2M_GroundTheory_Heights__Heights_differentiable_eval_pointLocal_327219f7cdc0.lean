-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_differentiable_eval_pointLocal_327219f7cdc0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:36.740553+00:00
-- url     : https://prove2.me/submissions/7f9d7c8b-da37-4138-bfb0-e34c5d039e45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Fintype σ] (q : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z : σ → ℂ ↦ eval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)
end GroundTheory.Heights₂.Heights
