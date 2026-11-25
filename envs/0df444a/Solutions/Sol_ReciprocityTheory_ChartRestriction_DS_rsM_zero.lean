-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rsM_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:33.206539+00:00
-- url     : https://prove2.me/submissions/c8de07f3-61cb-47c2-9410-cfa1753799bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {n : ℕ} : rsM (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) 0 (v : EH n) = (0 : EH n)
  rw [map_zero]
  rfl
end ReciprocityTheory.ChartRestriction.DS
