-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_filter_eq_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:40.639724+00:00
-- url     : https://prove2.me/submissions/b1d099d5-3b00-4c78-82d4-4142cff26598

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
theorem _root_.solution (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    univ.filter (fun b => ε b = ε a) = plusIdx ε := by
  have h : ε a = true := by simpa [plusIdx] using ha
  ext b
  simp [plusIdx, h]
end ReciprocityTheory.ChartRestriction.DS
