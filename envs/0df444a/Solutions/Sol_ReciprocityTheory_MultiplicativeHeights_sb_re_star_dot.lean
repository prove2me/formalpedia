-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_re_star_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:35.231916+00:00
-- url     : https://prove2.me/submissions/0259d906-2eb0-476b-bc68-520b9febb8bf

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA

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
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = normSq v := by
  unfold normSq dotProduct
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast
end ReciprocityTheory.MultiplicativeHeights
