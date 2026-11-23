-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ap_cutExt_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:27.685691+00:00
-- url     : https://prove2.me/submissions/a702058f-2c9c-4352-896b-f3c81d9cef4d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_gt_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ)
    (ε : ℝ) (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (x : M)
    (hx : ev n g ph r x < m) :
    cutExt n z g ph r c W χ ε =ᶠ[𝓝 x] fun y => (χ (ev n g ph r y / ε ^ 2) : ℂ) *
      ((∑ p ∈ hS.toFinset, if x ∈ W p then c p else 0) * jac n z g y) := by
  filter_upwards [ap_gt_local n z g ph r c W m hS hW x hx] with y hy
  simp only [cutExt, hy]
end ReciprocityTheory.L2DbarEstimates.I
