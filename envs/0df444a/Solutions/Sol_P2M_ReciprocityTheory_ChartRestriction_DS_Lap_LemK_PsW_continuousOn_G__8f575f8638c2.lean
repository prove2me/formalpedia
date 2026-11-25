-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_PsW_continuousOn_G__8f575f8638c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:42.316175+00:00
-- url     : https://prove2.me/submissions/f70b5b44-9845-42f9-a301-63c3066efd93

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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (D : List MM) :
    ContinuousOn (fun p : 𝕄 × KG ε => G' T μ D p.1 p.2) (Ps1.Uset ε ×ˢ Set.univ) := by
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
  have hFd : ContinuousOn (fun p : 𝕄 × KG ε => fderiv ℂ (Fw μ D) (psi p.2 p.1))
      (Ps1.Uset ε ×ˢ Set.univ) :=
    ((contDiffOn_Fw μ D).continuousOn_fderiv_of_isOpen isOpen_Om le_top).comp
      continuous_psi.continuousOn (fun ⦃p⦄ hp => hp.1 p.2)
  refine continuousOn_clm_apply.2 fun y => ?_
  have hdy : Continuous fun p : 𝕄 × KG ε => dpsi p.2 y := by
    first
    | exact continuous_const.prodMk
        (continuous_mmul (continuous_mmul (h2.comp continuous_snd) continuous_const) (h1.comp continuous_snd))
    | exact continuous_const.prod_mk
        (continuous_mmul (continuous_mmul (h2.comp continuous_snd) continuous_const) (h1.comp continuous_snd))
  exact (hFd.clm_apply hdy.continuousOn).smul (hC.comp continuous_snd).continuousOn
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.PsW
