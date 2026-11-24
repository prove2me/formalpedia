-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:54.191181+00:00
-- url     : https://prove2.me/submissions/1cfe50c7-a8b4-451b-9e1f-22ce78957360

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_add_le_fb366f40db4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3


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
theorem _root_.solution {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ r) :
    gaussNormOf (normAbv L) (∑ b ∈ s, f b) ≤ r :=
  Finset.sum_induction f (fun x ↦ gaussNormOf (normAbv L) x ≤ r)
    (fun _ _ ha hb ↦ (gaussNorm_add_le _ _).trans (max_le ha hb))
    (by rw [gaussNormOf_zero]; exact hr) h
end GroundTheory.Heights₂.Heights.GaussNormBasic
