-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.contDiffAt_phiP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:29.955703+00:00
-- url     : https://prove2.me/submissions/f33b0c9b-bbcf-4ff6-b48a-9063369566d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_contDiffAt_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_contDiff_lead

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
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution (μ : Fin n → ℤ) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    ContDiffAt ℂ 1 (PhiP μ) z := by
  show ContDiffAt ℂ 1 (fun y : 𝕄 => ∏ i : Fin n, lead ((i : ℕ) + 1) y ^ (-(μ i - muNext μ i))) z
  exact contDiffAt_prod fun i _ => contDiffAt_zpow (contDiff_lead _).contDiffAt (hz i) _
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
