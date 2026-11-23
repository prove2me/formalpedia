-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.continuous_Gk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:52.448463+00:00
-- url     : https://prove2.me/submissions/695066cc-7f70-4c1a-bbc1-d3b1399a382e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_Fwk

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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous (G T μ D z) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hC : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hop.mul continuous_const).mul (hop.comp continuous_inv)
  exact (continuous_Fwk μ D hz).smul hC
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
