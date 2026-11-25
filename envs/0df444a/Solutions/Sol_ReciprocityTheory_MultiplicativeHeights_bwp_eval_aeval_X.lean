-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_eval_aeval_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:36.952561+00:00
-- url     : https://prove2.me/submissions/98220d6b-94e2-448e-8074-755f2d3027e0

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {σ : Type*} (L : ℂ[X]) (i : σ) (y : σ → ℂ) :
    MvPolynomial.eval y (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) L) = L.eval (y i) := by
  induction L using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp
end ReciprocityTheory.MultiplicativeHeights
