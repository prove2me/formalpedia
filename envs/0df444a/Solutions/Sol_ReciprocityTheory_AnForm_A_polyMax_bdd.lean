-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polyMax_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:33.896573+00:00
-- url     : https://prove2.me/submissions/18d375eb-e7d1-4e3a-af36-71945eb2df12

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
theorem _root_.solution (hφ : UpperSemicontinuousOn φ U) {t : ℝ} (h : closedBall z t ⊆ U) :
    BddAbove (φ '' closedBall z t) :=
  (hφ.mono h).bddAbove_of_isCompact (isCompact_closedBall z t)
end ReciprocityTheory.AnForm.A
