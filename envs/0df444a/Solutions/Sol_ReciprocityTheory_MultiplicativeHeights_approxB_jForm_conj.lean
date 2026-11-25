-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:01:22.427864+00:00
-- url     : https://prove2.me/submissions/f7d9c4f0-df34-4959-b5d1-eb5add9be013

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
theorem _root_.solution (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : conj (jForm p x y) = jForm p y x := by
  rw [jForm, jForm, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (k : ℕ) < p <;> simp [sgn, h, mul_comm]
end ReciprocityTheory.MultiplicativeHeights
