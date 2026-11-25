-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.zd_iter_two_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:42:23.806596+00:00
-- url     : https://prove2.me/submissions/2343189f-1a03-4681-bdc6-e48850d95078

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : E → F) (k : ℕ) (y : E) (m : Fin (k + 2) → E) :
    iteratedFDeriv ℂ (k + 2) f y m =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y (m 0) (m 1) (Fin.tail (Fin.tail m)) := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
    LinearIsometryEquiv.comp_fderiv]
  simp [Fin.tail, Fin.succ_zero_eq_one]
end ReciprocityTheory.L2DbarEstimates.Y
