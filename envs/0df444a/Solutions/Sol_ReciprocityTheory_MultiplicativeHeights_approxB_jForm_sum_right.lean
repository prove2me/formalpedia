-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:10.98207+00:00
-- url     : https://prove2.me/submissions/f39704a1-cefc-42cd-9aa6-5ec3e14a1b64

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
theorem _root_.solution (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (x : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p x (∑ j ∈ s, f j) = ∑ j ∈ s, jForm p x (f j) := by
  simp only [jForm, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm
end ReciprocityTheory.MultiplicativeHeights
