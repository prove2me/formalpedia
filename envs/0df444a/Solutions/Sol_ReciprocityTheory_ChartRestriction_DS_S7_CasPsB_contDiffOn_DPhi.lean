-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.contDiffOn_DPhi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:07.038888+00:00
-- url     : https://prove2.me/submissions/7af66b65-402d-46ca-b191-adff45df714e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_phiP_three
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
    ContDiffOn ℂ 2 (fderiv ℂ (Ps1.PhiP μ)) (OmegaSet n : Set 𝕄) := by
  have h : ContDiffOn ℂ 3 (Ps1.PhiP μ) (OmegaSet n : Set 𝕄) :=
    fun z hz => (contDiffAt_phiP_three μ hz).contDiffWithinAt
  exact h.fderiv_of_isOpen (m := 2) Ps1.isOpen_omega' (by norm_num)
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
