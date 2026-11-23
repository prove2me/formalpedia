-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.continuousOn_fderiv_phiP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:01.868674+00:00
-- url     : https://prove2.me/submissions/bda873ae-1e8f-4d99-9664-3112a9e5ef37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_contDiffAt_phiP
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_omega__9ea460878a6b

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
theorem _root_.solution (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (PhiP μ)) (OmegaSet n : Set 𝕄) :=
  ContDiffOn.continuousOn_fderiv_of_isOpen (fun _ hz => (contDiffAt_phiP μ hz).contDiffWithinAt)
    isOpen_omega' le_rfl
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
