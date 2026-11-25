-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_apply_eval_397ad03046bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:46.573795+00:00
-- url     : https://prove2.me/submissions/0f76afd6-f891-4163-953a-6075da6fd37f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {σ : Type*} (w : σ → K' → ℕ) (d : σ →₀ ℕ) (k' : K') :
    Finsupp.weight w d k' = Finsupp.weight (fun v => w v k') d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
end GroundTheory.Heights₂.Heights.FieldNumbers
