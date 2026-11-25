-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BranchInComponent_differentiable_eval_a74d15f8973d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:18.128919+00:00
-- url     : https://prove2.me/submissions/98e3575b-cab8-49cb-87a6-8edb4caae04a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchInComponent

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
open MvPolynomial ComplexSets Metric Filter Topology Set
noncomputable section
open GroundTheory.Heights₂.Heights.BranchInComponent
namespace GroundTheory.Heights₂.Heights.BranchInComponent
theorem _root_.solution {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => eval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [eval_C]; exact differentiable_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (differentiable_apply i)
end GroundTheory.Heights₂.Heights.BranchInComponent
