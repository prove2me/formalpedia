-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.hasFDerivAt_lhol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:43.316551+00:00
-- url     : https://prove2.me/submissions/19c194c4-aca3-45f1-8b7b-bd7ac8e84cd1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_hasFDerivAt_integral_K
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_FY_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contOn_FY
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_lhol_psM_eq

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
variable [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
variable (hU : IsOpen U) (hΩ : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
  (hfd : ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
          (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
include hU hΩ hfd
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution (Y : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ U) :
    HasFDerivAt (fun x : 𝕄 => Lhol Y (psM T μ) x)
      (((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) • ∫ k, FY' T μ Y z k ∂(muK ε)) z := by
  obtain ⟨hF, hF'⟩ := contOn_FY T μ Y hΩ
  have hG := (hasFDerivAt_integral_K hU (FY T μ Y) (FY' T μ Y) hF hF'
    (fun x hx k => (FY_facts T μ Y k (hΩ x hx k)).1) hz).const_smul
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))
  have hU' : IsOpen (U : Set 𝕄) := hU
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [hU'.mem_nhds hz] with x hx using lhol_psM_eq T μ hfd Y hx
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
