-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.scaled_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:11.436918+00:00
-- url     : https://prove2.me/submissions/da308b7b-8346-4c0b-9e4d-d6603a427c7f

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
theorem _root_.solution (ε : ℝ) : ContDiff ℝ ∞ (ρ.scaled ε) :=
  contDiff_const.mul (ρ.contDiff.comp (contDiff_id.const_smul ε⁻¹))
end ReciprocityTheory.AnForm.A
