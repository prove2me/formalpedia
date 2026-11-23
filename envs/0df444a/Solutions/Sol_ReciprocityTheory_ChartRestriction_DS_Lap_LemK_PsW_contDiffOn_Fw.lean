-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW.contDiffOn_Fw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:52.797139+00:00
-- url     : https://prove2.me/submissions/c0017374-ca5d-47b9-b1da-bd3cb58b75be

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_contDiff_mmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_diffAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_contDiffOn_phiQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_isOpen_Om
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_hasFDerivAt_slice

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
theorem _root_.solution (μ : Fin n → ℤ) : ∀ D : List MM, ContDiffOn ℂ ω (Fw μ D) Om
  | [] => (contDiffOn_phiQ μ).comp contDiff_snd.contDiffOn fun _ hq => hq
  | Z :: D => by
    have hD := solution μ D
    have h1 : ContDiffOn ℂ ω (fderiv ℂ (Fw μ D)) Om := hD.fderiv_of_isOpen isOpen_Om le_top
    have h2 : ContDiff ℂ ω fun q : WW => ((0 : 𝕄 × 𝕄), mmul (mmul (mmul q.1.1 Z) q.1.2) q.2) :=
      contDiff_const.prodMk (contDiff_mmul (contDiff_mmul (contDiff_mmul
        (contDiff_fst.comp contDiff_fst) contDiff_const) (contDiff_snd.comp contDiff_fst)) contDiff_snd)
    refine (h1.clm_apply h2.contDiffOn).congr fun q hq => ?_
    show fderiv ℂ (fun y : 𝕄 => Fw μ D (q.1, y)) q.2 (mmul (mmul (mmul q.1.1 Z) q.1.2) q.2) = _
    rw [(hasFDerivAt_slice (diffAt hD isOpen_Om hq)).fderiv]
    rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
