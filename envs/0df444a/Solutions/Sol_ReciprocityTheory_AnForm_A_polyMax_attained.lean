-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polyMax_attained
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:34.079932+00:00
-- url     : https://prove2.me/submissions/b481aad7-9013-481a-827d-3cfa43729de7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a

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
theorem _root_.solution (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (ht : 0 ≤ t)
    (h : closedBall z t ⊆ U) : ∃ x ∈ closedBall z t, φ x = polyMax φ z t := by
  obtain ⟨a, ha, hmax⟩ := (hφ.mono h).exists_isMaxOn (nonempty_closedBall.2 ht)
    (isCompact_closedBall z t)
  exact ⟨a, ha, le_antisymm (le_polyMax hφ h ha)
    (polyMax_le' ht fun x hx => isMaxOn_iff.1 hmax x hx)⟩
end ReciprocityTheory.AnForm.A
