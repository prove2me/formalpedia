-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_contDiffAt_zpow__7b37fef72d3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:47.807795+00:00
-- url     : https://prove2.me/submissions/2b17a22f-560a-46bd-bbf7-59ebd4ce4d10

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
theorem _root_.solution {f : 𝕄 → ℂ} {x : 𝕄} {m : ℕ∞ω}
    (hf : ContDiffAt ℂ m f x) (hx : f x ≠ 0) (k : ℤ) : ContDiffAt ℂ m (fun y => f y ^ k) x := by
  obtain ⟨m', rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hf.pow m'
  · have h1 : ContDiffAt ℂ m (fun y => (f y ^ m')⁻¹) x := (hf.pow m').inv (pow_ne_zero _ hx)
    simpa using h1
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
