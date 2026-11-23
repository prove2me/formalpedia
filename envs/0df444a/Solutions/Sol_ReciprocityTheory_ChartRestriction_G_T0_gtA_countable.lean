-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.gtA_countable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:41.629854+00:00
-- url     : https://prove2.me/submissions/056ce8f6-663b-4c2f-948a-ebfe810f89ee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Countable (span ℤ (Set.range B)).toAddSubgroup := by
  have e : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      Set.range (fun c : Fin n → ℤ => ∑ i, c i • B i) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  have hc : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)).Countable := by
    rw [e]
    exact Set.countable_range _
  exact hc.to_subtype
end ReciprocityTheory.ChartRestriction.G.T0
