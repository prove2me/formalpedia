-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_G_k_2cdb220cc1dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:16.993125+00:00
-- url     : https://prove2.me/submissions/1f4c007e-65b6-4ed9-8172-aee5006a5d20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_PsWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuous_mmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_isOpen_Om
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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) {z : 𝕄} (hz : z ∈ Ps1.Uset ε) :
    Continuous (G' T μ D z) := by
  have h1 : Continuous fun k : KG ε => toMK k := by
    first
    | fun_prop
    | (unfold toMK; fun_prop)
    | continuity
    | (unfold toMK; continuity)
  have h2 : Continuous fun k : KG ε => toMK k⁻¹ := h1.comp continuous_inv
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hC : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    (hop.mul continuous_const).mul (hop.comp continuous_inv)
  have hps : Continuous fun k : KG ε => psi k z := by
    first
    | exact continuous_psi.comp (Continuous.prodMk continuous_const continuous_id)
    | exact continuous_psi.comp (Continuous.prod_mk continuous_const continuous_id)
  have hFd : Continuous fun k : KG ε => fderiv ℂ (Fw μ D) (psi k z) :=
    ((contDiffOn_Fw μ D).continuousOn_fderiv_of_isOpen isOpen_Om le_top).comp_continuous hps
      (fun k => hz k)
  refine continuous_clm_apply.2 fun y => ?_
  have hdy : Continuous fun k : KG ε => dpsi k y := by
    first
    | exact continuous_const.prodMk (continuous_mmul (continuous_mmul h2 continuous_const) h1)
    | exact continuous_const.prod_mk (continuous_mmul (continuous_mmul h2 continuous_const) h1)
  exact (hFd.clm_apply hdy).smul hC
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
