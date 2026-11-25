-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.csq_two_rhoHol_minus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:41.714351+00:00
-- url     : https://prove2.me/submissions/ffeabaa2-e94e-4a1f-a69a-90b7c4d9c5e2

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
theorem _root_.solution (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = -(pOf ε : ℂ) := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  rw [show rhoHol ε a = -(pOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.DS
