-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:38.195373+00:00
-- url     : https://prove2.me/submissions/5f366d0f-b85c-47b3-96dd-9c162ef0418d

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
theorem _root_.solution (hφ : UpperSemicontinuousOn φ U) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h : closedBall z t ⊆ U) : polyMax φ z s ≤ polyMax φ z t :=
  csSup_le_csSup (polyMax_bdd hφ h) ((nonempty_closedBall.2 hs).image φ)
    (image_mono (closedBall_subset_closedBall hst))
end ReciprocityTheory.AnForm.A
