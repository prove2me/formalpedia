-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.scaled_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:59.666458+00:00
-- url     : https://prove2.me/submissions/28324a2e-19dd-4c12-b50b-42b568bd25a7

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
variable (ρ : Mollifier D)
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (w : Fin D → ℂ) : 0 ≤ ρ.scaled ε w :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le _)) (ρ.nonneg _)
end ReciprocityTheory.AnForm.A
