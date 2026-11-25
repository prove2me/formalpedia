-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_val_le_iff_div_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:51.520964+00:00
-- url     : https://prove2.me/submissions/4801c19f-e3b3-491a-aa9c-49b05220323b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {U : Type} [Field U] (V : ValuationSubring U) {x y : U} (hy : y ≠ 0) :
    V.valuation x ≤ V.valuation y ↔ x / y ∈ V := by
  have hy0 : (0 : _) < V.valuation y := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hy)
  rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ hy0]
end ReciprocityTheory.MultiplicativeHeights
