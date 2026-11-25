-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isNCSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:36.643182+00:00
-- url     : https://prove2.me/submissions/7c92d0c9-4bfb-4470-a497-3c0ce30df788

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics

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
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ν : Fin n → ℝ} : IsNCSum ε 0 ν ↔ ν = 0 := by
  constructor
  · rintro ⟨γ, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩
end ReciprocityTheory.ChartRestriction.DS
