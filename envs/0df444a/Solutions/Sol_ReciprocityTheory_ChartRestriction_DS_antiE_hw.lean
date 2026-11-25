-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.antiE_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:44.282897+00:00
-- url     : https://prove2.me/submissions/4b22e553-035b-4991-bc6c-df5db8bbb45f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep

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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} {ν : Fin n → ℝ} {v : M} (hv : IsHWVec E ν v) :
    IsHWVec (antiE E) (fun r => -ν (Fin.rev r)) v := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp [antiE, hv.1 (Fin.rev a)]
  · simp [antiE, hv.2 (Fin.rev b) (Fin.rev a) (Fin.rev_lt_rev.mpr hab)]
end ReciprocityTheory.ChartRestriction.DS
