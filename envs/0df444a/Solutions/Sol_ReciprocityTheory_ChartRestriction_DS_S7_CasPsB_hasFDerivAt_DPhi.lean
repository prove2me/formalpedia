-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.hasFDerivAt_DPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:38.258272+00:00
-- url     : https://prove2.me/submissions/8dd3a3c4-694b-4bf4-adcb-fa5e24be3e79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffOn_DPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_isOpen_omega


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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution (μ : Fin n → ℤ) {w : 𝕄} (hw : w ∈ OmegaSet n) :
    HasFDerivAt (fderiv ℂ (Ps1.PhiP μ)) (fderiv ℂ (fderiv ℂ (Ps1.PhiP μ)) w) w := (((contDiffOn_DPhi μ).differentiableOn (by norm_num) w hw).differentiableAt (isOpen_omega.mem_nhds hw)).hasFDerivAt
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
