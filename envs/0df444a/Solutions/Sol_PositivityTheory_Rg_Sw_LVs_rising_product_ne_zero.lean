-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.rising_product_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:23.011802+00:00
-- url     : https://prove2.me/submissions/b1ed70f6-c573-4b41-9225-553f6fe95169

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (a : ℤ) (m : ℕ) (h : ∀ i : ℕ, i < m → (i : ℤ) + a ≠ 0) :
    ∏ i ∈ Finset.range m, ((a : ℂ) + (i : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply h i (Finset.mem_range.1 hi)
  have : (((i : ℤ) + a : ℤ) : ℂ) = 0 := by push_cast; linear_combination h0
  exact_mod_cast this
end PositivityTheory.Rg.Sw.LVs
