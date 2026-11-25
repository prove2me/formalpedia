-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.continuousOn_D2Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:17.510268+00:00
-- url     : https://prove2.me/submissions/796d22be-0e44-481e-a45b-4e8e520f9da7

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
theorem _root_.solution (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (fderiv ℂ (Ps1.PhiP μ))) (OmegaSet n : Set 𝕄) := (contDiffOn_DPhi μ).continuousOn_fderiv_of_isOpen isOpen_omega (by norm_num)
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
