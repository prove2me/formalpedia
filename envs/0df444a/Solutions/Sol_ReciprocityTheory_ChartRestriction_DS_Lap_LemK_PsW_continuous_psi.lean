-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.continuous_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:59.868705+00:00
-- url     : https://prove2.me/submissions/12c6a415-0242-4e18-b873-e6637870777a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_mmul

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
theorem _root_.solution : Continuous fun p : 𝕄 × KG ε => psi p.2 p.1 := by
  have h1 : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | continuity
    | (unfold toMK; continuity)
  have h2 : Continuous fun k : KG ε => toMK k⁻¹ := h1.comp continuous_inv
  have hm : Continuous fun p : 𝕄 × KG ε => mmul (mmul (toMK p.2⁻¹) p.1) (toMK p.2) :=
    continuous_mmul (continuous_mmul (h2.comp continuous_snd) continuous_fst) (h1.comp continuous_snd)
  first
  | exact ((h2.comp continuous_snd).prodMk (h1.comp continuous_snd)).prodMk hm
  | exact ((h2.comp continuous_snd).prod_mk (h1.comp continuous_snd)).prod_mk hm
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
