-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rsM_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:07.354514+00:00
-- url     : https://prove2.me/submissions/22c45189-33c9-4dae-bfb8-829659bed6bf

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
theorem _root_.solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A - rsM B = rsM (A - B) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) - toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A - B) (v : EH n)
  rw [map_sub]
  rfl
end ReciprocityTheory.ChartRestriction.DS
