-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.isNCSum_succ_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:53.724669+00:00
-- url     : https://prove2.me/submissions/c56a11c3-5a2e-4586-b52e-08c06bf4a64c

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
theorem _root_.solution {k : ℕ} {ν : Fin n → ℝ} (hν : IsNCSum ε (k + 1) ν) :
    ∃ a b : Fin n, ε a ≠ ε b := by
  obtain ⟨γ, hγ, -⟩ := hν
  exact ⟨_, _, hγ 0⟩
end ReciprocityTheory.ChartRestriction.DS
