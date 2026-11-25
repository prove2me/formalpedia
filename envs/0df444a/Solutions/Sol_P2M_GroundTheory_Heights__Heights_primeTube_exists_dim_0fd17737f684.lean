-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_primeTube_exists_dim_0fd17737f684
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:47.845682+00:00
-- url     : https://prove2.me/submissions/f1ac6055-9eb1-4963-8a27-fb0319a602ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeTubeVolume

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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ)) :
    ∃ d : ℕ, d ≤ k ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) := by
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hnn hk ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at hnn
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast] at hk
      exact absurd (WithBot.coe_le_coe.1 hk) (by simp)
    | coe m => exact ⟨m, by exact_mod_cast hk, by norm_cast⟩
end GroundTheory.Heights₂.Heights
