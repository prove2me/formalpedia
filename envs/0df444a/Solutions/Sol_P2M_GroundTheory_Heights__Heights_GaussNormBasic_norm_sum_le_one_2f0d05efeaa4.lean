-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_norm_sum_le_one_2f0d05efeaa4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:59:03.681946+00:00
-- url     : https://prove2.me/submissions/dffa41c8-a310-4fb6-9d2d-965ddd03eba0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]
namespace GroundTheory.Heights₂.Heights.GaussNormBasic
theorem _root_.solution {β : Type*} (s : Finset β) (f : β → L) (h : ∀ b ∈ s, ‖f b‖ ≤ 1) :
    ‖∑ b ∈ s, f b‖ ≤ 1 :=
  Finset.sum_induction f (fun x ↦ ‖x‖ ≤ 1)
    (fun _ _ ha hb ↦ (IsUltrametricDist.isNonarchimedean_norm _ _).trans (max_le ha hb))
    (by simp) h
end GroundTheory.Heights₂.Heights.GaussNormBasic
