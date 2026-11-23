-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.contDiff_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:21.738228+00:00
-- url     : https://prove2.me/submissions/017724e4-7f9c-4a66-bde9-6ef80304668a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (a b : Fin n) {m : ℕ∞ω} :
    ContDiff ℂ m (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
  exact (contDiff_apply ℂ ℂ b).comp (contDiff_apply ℂ (Fin n → ℂ) a)
end ReciprocityTheory.ChartRestriction.DS.S7
