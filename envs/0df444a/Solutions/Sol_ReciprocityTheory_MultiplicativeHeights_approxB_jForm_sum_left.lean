-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:16:36.253315+00:00
-- url     : https://prove2.me/submissions/5a013c5c-965f-43a3-a199-3fe78cd86444

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA

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
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (y : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  simp only [jForm, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm
end ReciprocityTheory.MultiplicativeHeights
