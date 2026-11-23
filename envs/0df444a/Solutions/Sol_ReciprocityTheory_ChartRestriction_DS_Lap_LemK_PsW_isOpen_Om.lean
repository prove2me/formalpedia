-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.isOpen_Om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:15.832662+00:00
-- url     : https://prove2.me/submissions/0b7a811e-54b6-4119-a199-e01a619eb530

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_contDiff_lead
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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
theorem _root_.solution : IsOpen (Om : Set WW) := by
  have ho : IsOpen (OmegaSet n : Set 𝕄) := by
    show IsOpen {z : 𝕄 | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ne_fun (contDiff_lead (n := n) _).continuous continuous_const
  exact ho.preimage continuous_snd
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
