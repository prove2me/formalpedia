-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_re_dot_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:47.100219+00:00
-- url     : https://prove2.me/submissions/cea63576-8003-40e0-ae53-eaac1490d6e1

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallC

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
open Matrix Module
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re = (star w ⬝ᵥ v).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring
end ReciprocityTheory.MultiplicativeHeights
