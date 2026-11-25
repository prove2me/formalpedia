-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rsM_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:04.009002+00:00
-- url     : https://prove2.me/submissions/6ae0b06c-e05a-410a-a912-51ee6ed60ba3

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : rsM (-A) = -rsM A := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (-A) (v : EH n) = -toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n)
  rw [map_neg]
  rfl
end ReciprocityTheory.ChartRestriction.DS
