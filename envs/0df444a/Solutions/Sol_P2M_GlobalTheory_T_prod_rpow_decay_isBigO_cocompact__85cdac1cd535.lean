-- Prove2me | solution 1 for P2M_GlobalTheory_T_prod_rpow_decay_isBigO_cocompact__85cdac1cd535
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:33:56.346707+00:00
-- url     : https://prove2.me/submissions/571facb3-138e-49c2-81c1-006be0dac100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdRpowDecayIsBigOCocompactStatement
import Theorems.Thm_GlobalTheory_prod_rpow_decay_isBigO_cocompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  first | exact @GlobalTheory.prod_rpow_decay_isBigO_cocompact | exact GlobalTheory.prod_rpow_decay_isBigO_cocompact | (intros; apply GlobalTheory.prod_rpow_decay_isBigO_cocompact <;> assumption)
end _root_.GlobalTheory.T
