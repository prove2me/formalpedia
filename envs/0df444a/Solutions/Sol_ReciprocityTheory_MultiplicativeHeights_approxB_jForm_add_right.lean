-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:06.305052+00:00
-- url     : https://prove2.me/submissions/802721eb-b80d-4d13-93b6-f156763e4457

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
theorem _root_.solution (p : ℕ) {r : ℕ} (x y z : Fin r → ℂ) :
    jForm p x (y + z) = jForm p x y + jForm p x z := by
  simp only [jForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]
end ReciprocityTheory.MultiplicativeHeights
