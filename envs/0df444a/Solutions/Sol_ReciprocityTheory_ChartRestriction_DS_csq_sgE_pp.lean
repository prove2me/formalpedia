-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_sgE_pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:54.177095+00:00
-- url     : https://prove2.me/submissions/74d23087-2b82-4655-b7b7-99a9bf4343f9

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
    (ha : a ∈ plusIdx ε) (hb : b ∈ plusIdx ε) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  have hb' : ε b = true := by simpa [plusIdx] using hb
  simp [sgE, ha', hb']
end ReciprocityTheory.ChartRestriction.DS
