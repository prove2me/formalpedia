-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.hasFDerivAt_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:49.900633+00:00
-- url     : https://prove2.me/submissions/5a736a8f-b075-4c45-8baa-4a6b0130c31b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord

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
theorem _root_.solution (k : KG ε) (z : 𝕄) : HasFDerivAt (psi k) (dpsi k) z := by
  first
  | exact (hasFDerivAt_const (toMK k⁻¹, toMK k) z).prodMk
      (Ps1.conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt
  | exact (hasFDerivAt_const (toMK k⁻¹, toMK k) z).prod
      (Ps1.conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
