-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_sgE_mm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:08.91655+00:00
-- url     : https://prove2.me/submissions/d432c9e4-04f6-4f84-af2f-8e4756ecc409

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ minusIdx ε) (hb : b ∈ minusIdx ε) :
    sgE ε cp cm a b = -∑ i ∈ plusIdx ε, cp i b * cm i a := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  have hb' : ε b = false := by simpa [minusIdx] using hb
  simp [sgE, ha', hb']
end ReciprocityTheory.ChartRestriction.DS
