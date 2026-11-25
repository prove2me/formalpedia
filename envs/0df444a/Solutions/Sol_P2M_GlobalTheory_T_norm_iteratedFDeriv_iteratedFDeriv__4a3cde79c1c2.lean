-- Prove2me | solution 1 for P2M_GlobalTheory_T_norm_iteratedFDeriv_iteratedFDeriv__4a3cde79c1c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:30.625823+00:00
-- url     : https://prove2.me/submissions/6fa2080c-4ad9-4bf8-8127-986ada83d7c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivIteratedFDerivStatement
import Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_iteratedFDeriv


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
theorem _root_.solution : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (n j : ℕ) (z : E), ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ n f) z‖ = ‖iteratedFDeriv ℝ (n + j) f z‖ := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | exact GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv | (intros; apply GlobalTheory.norm_iteratedFDeriv_iteratedFDeriv <;> assumption)
end _root_.GlobalTheory.T
