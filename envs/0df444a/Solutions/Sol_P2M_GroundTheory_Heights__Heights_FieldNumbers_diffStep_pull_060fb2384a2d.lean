-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_pull_060fb2384a2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:57.735401+00:00
-- url     : https://prove2.me/submissions/67fe4003-979d-4316-8eab-2b8a754e0da1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_some_4a0cbc5e102b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_none_b7c995227689

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (c : K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (pullDeg Function.Embedding.some c) (prodFn A B) = prodFn (diffStep c A) B := by
  funext m
  have h1 : (fun k => (m - pullDeg Function.Embedding.some c) (some k)) =
      (fun k => m (some k)) - c := by
    funext k
    simp [pullDeg_some]
  have h2 : (m - pullDeg Function.Embedding.some c) none = m none := by
    simp [pullDeg_none]
  unfold diffStep prodFn
  rw [h1, h2]
  ring
end GroundTheory.Heights₂.Heights.FieldNumbers
