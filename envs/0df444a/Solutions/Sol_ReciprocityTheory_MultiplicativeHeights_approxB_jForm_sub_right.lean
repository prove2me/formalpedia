-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:10.745463+00:00
-- url     : https://prove2.me/submissions/e50c8ad0-6821-4fa9-b443-34a59e8b7d72

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
    jForm p x (y - z) = jForm p x y - jForm p x z := by
  simp only [jForm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
end ReciprocityTheory.MultiplicativeHeights
