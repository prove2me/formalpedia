-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.integrable_gprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:37:49.547286+00:00
-- url     : https://prove2.me/submissions/755fb0b4-b640-4f67-b317-c8a3834fffa9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_gF_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (p q : ι) {β : ℝ} (hβ : β < 1) :
    Integrable (fun x : ι → ℂ => ∏ i, gF p q β i (x i)) := by
  first
  | exact Integrable.fintype_prod (f := fun i => gF p q β i) (fun i => gF_integrable p q hβ i)
  | exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i)
  | (rw [volume_pi]; exact Integrable.fintype_prod (fun i => gF_integrable p q hβ i))
  | exact Integrable.fintype_prod_dep (fun i => gF_integrable p q hβ i)
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
