-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.radialBump_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:37.017611+00:00
-- url     : https://prove2.me/submissions/b183758e-d2cd-4aaa-8ff9-a20c73376b6d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMol
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshMol
theorem _root_.solution (D : ℕ) (c : ℂ) (w : Fin D → ℂ) (hc : ‖c‖ = 1) : g0 D (c • w) = g0 D w := by
  simp [g0, norm_mul, hc]
end ReciprocityTheory.AnForm.A.PshMol
