-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_1cf518418e18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:49.551526+00:00
-- url     : https://prove2.me/submissions/ae255e8d-0092-4b47-bad5-4df8ff20f51c

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
variable [DecidableEq K] [DecidableEq K']
omit [DecidableEq K] [DecidableEq K']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (g : σ → τ)
    (d : σ →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain g d) = Finsupp.weight (w ∘ g) d := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
