-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.contDiffAt_phiP_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:20:12.598811+00:00
-- url     : https://prove2.me/submissions/3a8d058e-a2f2-4181-8f24-af6e4a07aab7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiff_lead__3735fe896cb7
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_zpow__7b37fef72d3e

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
theorem _root_.solution (μ : Fin n → ℤ) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    ContDiffAt ℂ 3 (Ps1.PhiP μ) z := by
  show ContDiffAt ℂ 3 (fun y : 𝕄 => ∏ i : Fin n, lead ((i : ℕ) + 1) y ^ (-(μ i - muNext μ i))) z
  exact contDiffAt_prod fun i _ => contDiffAt_zpow' (contDiff_lead' _).contDiffAt (hz i) _
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
