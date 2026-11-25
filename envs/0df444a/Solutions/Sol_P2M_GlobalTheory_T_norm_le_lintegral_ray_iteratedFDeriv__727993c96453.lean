-- Prove2me | solution 1 for P2M_GlobalTheory_T_norm_le_lintegral_ray_iteratedFDeriv__727993c96453
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:33.630495+00:00
-- url     : https://prove2.me/submissions/ae9686e6-b5ad-417c-bdd7-be5d11ee3404

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDerivStatement
import Theorems.Thm_GlobalTheory_norm_le_lintegral_ray_iteratedFDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E), ContDiff ℝ (⊤ : ℕ∞) G → (∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) → ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) * (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  first | exact @GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv | exact GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv | (intros; apply GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv <;> assumption)
end _root_.GlobalTheory.T
