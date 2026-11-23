-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.continuous_Fwk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:16.889165+00:00
-- url     : https://prove2.me/submissions/e96f2ad1-8b37-4de4-be85-ebe40fd97800

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_contDiffOn_Fw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
variable {n : ℕ}
local notation "𝕄" => Fin n → Fin n → ℂ
local notation "MM" => Matrix (Fin n) (Fin n) ℂ
local notation "WW" => ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) × (Fin n → Fin n → ℂ)
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous fun k : KG ε => Fw μ D (psi k z) := by
  have hc : Continuous fun k : KG ε => psi k z := by
    first
    | exact continuous_psi.comp (Continuous.prodMk continuous_const continuous_id)
    | exact continuous_psi.comp (Continuous.prod_mk continuous_const continuous_id)
  exact (contDiffOn_Fw μ D).continuousOn.comp_continuous hc (fun k => hz k)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
