-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_polyMax_zero__254d90a70d0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:47.494452+00:00
-- url     : https://prove2.me/submissions/70cb0173-4146-4274-ab7d-b28c935ec163

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll

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
theorem _root_.solution : polyMax φ z 0 = φ z := by
  simp [polyMax, closedBall_zero]
end ReciprocityTheory.AnForm.A
