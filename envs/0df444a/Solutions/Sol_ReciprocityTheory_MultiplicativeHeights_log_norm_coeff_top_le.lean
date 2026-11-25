-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.log_norm_coeff_top_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:47:21.705691+00:00
-- url     : https://prove2.me/submissions/c414e373-8b02-47f4-af0a-19a289bc222e

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_log_norm_leadingCoeff_le

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
open MeasureTheory Polynomial Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (htop : ∀ k', k < k' → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  have hd : p.natDegree = k := by
    apply le_antisymm
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun k' hk' => htop k' (by exact_mod_cast hk')
    · exact le_natDegree_of_ne_zero hk
  have := log_norm_leadingCoeff_le p
  rwa [leadingCoeff, hd] at this
end ReciprocityTheory.MultiplicativeHeights
