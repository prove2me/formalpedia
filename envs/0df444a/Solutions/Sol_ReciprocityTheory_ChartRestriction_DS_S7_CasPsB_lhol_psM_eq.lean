-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.lhol_psM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:59.992181+00:00
-- url     : https://prove2.me/submissions/4f6909a4-2dc4-44d3-95fd-77bf7cb673f1

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
variable [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution
    (hfd : ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
      ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
        ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
          (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
    (Y : Matrix (Fin n) (Fin n) ℂ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ U) :
    Lhol Y (psM T μ) x = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, FY T μ Y x k ∂(muK ε) := by
  show fderiv ℂ (psM T μ) x (Y * x) = _
  rw [hfd x hx]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  show fderiv ℂ (PhiM μ) _ (toMK k⁻¹ * (Y * x) * toMK k) • _ = FY T μ Y x k
  rw [← Matrix.mul_assoc (toMK k⁻¹) Y x]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
