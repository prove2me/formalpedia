-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ApproximationGraph.jForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:36:52.803275+00:00
-- url     : https://prove2.me/submissions/8acbc3c1-7d00-41c5-8ec1-75fa4e667456

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraphA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ApproximationGraph_inner_euc

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
theorem _root_.solution (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) :
    jForm p x y = inner ℂ (euc (posPart p x)) (euc (posPart p y)) -
      inner ℂ (euc (negPart p x)) (euc (negPart p y)) := by
  rw [inner_euc, inner_euc, ← Finset.sum_sub_distrib]
  unfold jForm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn, posPart, negPart]
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
