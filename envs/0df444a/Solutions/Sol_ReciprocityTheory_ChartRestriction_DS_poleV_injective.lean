-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.poleV_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:28.737123+00:00
-- url     : https://prove2.me/submissions/be7240b1-8dd8-4b26-8b2a-30d03d73af98

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
theorem _root_.solution {μ : Fin n → ℝ} (hμ : Function.Injective μ) : Function.Injective (poleV μ) := by
  intro x y h
  apply hμ
  simp only [poleV] at h
  have h' := Complex.ofReal_injective h
  linarith
end ReciprocityTheory.ChartRestriction.DS
