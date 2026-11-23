-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.radialBump_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:14.445592+00:00
-- url     : https://prove2.me/submissions/8a52bce1-3b39-45a4-8104-b6542d1ecb8b

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
theorem _root_.solution (D : ℕ) : ContDiff ℝ ∞ (g0 D) :=
  b0.contDiff.comp (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))
end ReciprocityTheory.AnForm.A.PshMol
