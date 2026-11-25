-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_norm_jForm_self_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:09.052313+00:00
-- url     : https://prove2.me/submissions/6c9284f8-dcfc-4851-b4d7-b2114f3ddc84

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_posSq_nonneg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_negSq_nonneg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_posSq_add_negSq
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
theorem _root_.solution (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖jForm p u u‖ ≤ normSq u := by
  rw [approxB_jForm_self, Complex.norm_real, Real.norm_eq_abs, ← approxB_posSq_add_negSq]
  have h1 := approxB_posSq_nonneg p u
  have h2 := approxB_negSq_nonneg p u
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
end ReciprocityTheory.MultiplicativeHeights
