-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.le_polyMax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:38.651869+00:00
-- url     : https://prove2.me/submissions/85e61e01-7c3c-42bf-8d3a-498d4d89bd3d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) {x}
    (hx : x ∈ closedBall z t) : φ x ≤ polyMax φ z t :=
  le_csSup (polyMax_bdd hφ h) (mem_image_of_mem φ hx)
end ReciprocityTheory.AnForm.A
