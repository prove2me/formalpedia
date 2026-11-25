-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_re_dot_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:06:46.258909+00:00
-- url     : https://prove2.me/submissions/0f4019f4-cd26-43ef-b179-a0412c676fb0

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_posSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_negSq_eq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_J
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix
private theorem re_star_dotProduct_self_eq_normSq {r : ℕ} (x : Fin r → ℂ) : (star x ⬝ᵥ x).re = normSq x := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, normSq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (star (x k) * x k).re = (x k).re * (x k).re + (x k).im * (x k).im := by
    simp [Complex.mul_re] <;> ring
  rw [h1, ← Complex.normSq_apply]
  first
    | exact (Complex.sq_norm _).symm
    | exact Complex.normSq_eq_norm_sq _
    | simp [Complex.sq_abs]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℕ) {r : ℕ} (v : Fin r → ℂ) :
    (star v ⬝ᵥ (signMat p r *ᵥ v)).re = posSq p v - negSq p v := by
  rw [sb_dot_J, Complex.sub_re, re_star_dotProduct_self_eq_normSq, re_star_dotProduct_self_eq_normSq, sb_posSq_eq, sb_negSq_eq]
end ReciprocityTheory.MultiplicativeHeights
