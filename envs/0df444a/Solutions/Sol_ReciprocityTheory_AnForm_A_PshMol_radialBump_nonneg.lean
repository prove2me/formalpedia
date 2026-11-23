-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.radialBump_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:15.069461+00:00
-- url     : https://prove2.me/submissions/669e827e-e0b0-4f9b-a670-5c8525405a3b

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
theorem _root_.solution (D : ℕ) (w : Fin D → ℂ) : 0 ≤ g0 D w := b0.nonneg
end ReciprocityTheory.AnForm.A.PshMol
