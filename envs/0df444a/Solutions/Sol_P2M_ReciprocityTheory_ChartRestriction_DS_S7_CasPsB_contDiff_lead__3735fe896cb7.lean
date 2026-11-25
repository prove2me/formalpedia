-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiff_lead__3735fe896cb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:51.321114+00:00
-- url     : https://prove2.me/submissions/72cf325c-03ba-4add-902c-df16b911e0a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB

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
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (fun z : 𝕄 => lead i z) := by
  by_cases h : i ≤ n
  · have e : (fun z : 𝕄 => lead i z) = fun z =>
        ∑ σ : Equiv.Perm (Fin i), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∏ j, z (Fin.castLE h (σ j)) (Fin.castLE h j) := by
      funext z
      simp only [lead, dif_pos h, Matrix.det_apply']
      rfl
    rw [e]
    exact ContDiff.sum fun σ _ => contDiff_const.mul
      (contDiff_prod fun j _ => contDiff_apply_apply ℂ ℂ _ _)
  · have e : (fun z : 𝕄 => lead i z) = fun _ => 0 := by
      funext z
      simp only [lead, dif_neg h]
    rw [e]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
