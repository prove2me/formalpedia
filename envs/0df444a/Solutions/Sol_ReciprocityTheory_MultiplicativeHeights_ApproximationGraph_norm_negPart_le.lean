-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.norm_negPart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:26:06.526535+00:00
-- url     : https://prove2.me/submissions/a52be2ac-997c-4249-a2b9-a58bde8f4dcc

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_normSq_eq_euc
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_negSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_normSq_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
open ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (negPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := negSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (negPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
