-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.poleVd_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:23:08.743835+00:00
-- url     : https://prove2.me/submissions/3c3ca70a-fd29-49d4-a0b3-ca0e35b3d554

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleVd μ) := by
  intro x y h
  apply hμ
  simp only [poleVd] at h
  have h' := Complex.ofReal_injective h
  linarith
end ReciprocityTheory.ChartRestriction.DS
