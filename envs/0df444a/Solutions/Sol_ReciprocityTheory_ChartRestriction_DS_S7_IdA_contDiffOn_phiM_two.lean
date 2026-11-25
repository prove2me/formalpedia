-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.IdA.contDiffOn_phiM_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:11.587251+00:00
-- url     : https://prove2.me/submissions/e3dff115-52ec-4254-9181-a8dc707c5cb0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.IdA
namespace ReciprocityTheory.ChartRestriction.DS.S7.IdA
theorem _root_.solution (μ : Fin n → ℤ) : ContDiffOn ℂ 2 (PhiM μ) (OmegaSet n) :=
  fun _ hz => (contDiffAt_phiM μ hz (m := 2)).contDiffWithinAt
end ReciprocityTheory.ChartRestriction.DS.S7.IdA
