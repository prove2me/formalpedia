-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dz_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:31.141656+00:00
-- url     : https://prove2.me/submissions/f1ffe9f6-e07f-4723-bcaf-4c1d23697578

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (h : f =ᶠ[𝓝 z] g) : dz j f z = dz j g z := by
  have e : fderiv ℝ f z = fderiv ℝ g z := Filter.EventuallyEq.fderiv_eq h
  unfold dz
  rw [e]
end ReciprocityTheory.AnForm.A
