-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_pad_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:10.6332+00:00
-- url     : https://prove2.me/submissions/7ed1a38c-fc9c-430e-a2c1-5544df461b71

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_sum_pos

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
theorem _root_.solution {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (X : Fin r → Fin r → ℂ) :
    ∑ j, approxPadPos x j • X j = ∑ k : ApproxPosIdx r p, x k • X k.1 := by
  rw [approxB_sum_pos (p := p) _ (fun j hj => by simp [approxPadPos, hj])]
  exact Finset.sum_congr rfl fun k _ => by simp [approxPadPos, k.2]
end ReciprocityTheory.MultiplicativeHeights
