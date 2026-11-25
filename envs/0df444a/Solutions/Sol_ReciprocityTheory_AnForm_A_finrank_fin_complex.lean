-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.finrank_fin_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:13.967656+00:00
-- url     : https://prove2.me/submissions/86b519b1-ba1d-4203-9528-c5b476102920

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollA

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
open scoped ContDiff Convolution
noncomputable section
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by
  rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm]
end ReciprocityTheory.AnForm.A
