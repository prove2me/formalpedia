-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:01:40.741302+00:00
-- url     : https://prove2.me/submissions/9cf19329-a98c-4418-b219-ed71a9ce1fea

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {σ τ : Type*} (v : σ → MvPolynomial τ ℂ) (x : τ → ℂ)
    (g : MvPolynomial σ ℂ) : eval x (aeval v g) = eval (fun i => eval x (v i)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, eval_X, hp]
end ReciprocityTheory.MultiplicativeHeights
