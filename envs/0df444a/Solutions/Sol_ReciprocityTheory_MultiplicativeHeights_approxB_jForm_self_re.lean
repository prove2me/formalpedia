-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_jForm_self_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:56.046703+00:00
-- url     : https://prove2.me/submissions/6d7a3a3d-54af-450d-b34f-11306c85cd07

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_jForm_self

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
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    (jForm p u u).re = posSq p u - negSq p u := by
  rw [approxB_jForm_self, Complex.ofReal_re]
end ReciprocityTheory.MultiplicativeHeights
