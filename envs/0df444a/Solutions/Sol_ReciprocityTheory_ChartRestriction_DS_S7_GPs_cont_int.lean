-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.cont_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:23:11.256276+00:00
-- url     : https://prove2.me/submissions/6741c6ac-babc-43a7-928c-bc0a0ee4b8ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_continuous_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_emb_mem

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
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
local notation "𝕄f" => Fin n → Fin n → ℂ
variable {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ) (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Ps1.Uset ε) : Continuous fun k => g (emb x k) • Pk T k := by
  have hop : Continuous (fun k : KG ε => T.op k) := continuous_subtype_val.comp T.cont
  have hPk : Continuous (Pk T) := (hop.mul continuous_const).mul (hop.comp continuous_inv)
  have he : Continuous (fun k : KG ε => emb x k) := continuous_emb.comp (continuous_const.prodMk continuous_id)
  have hgc : Continuous (fun k => g (emb x k)) := hg.continuousOn.comp_continuous he (fun k => emb_mem hx k)
  exact hgc.smul hPk
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
