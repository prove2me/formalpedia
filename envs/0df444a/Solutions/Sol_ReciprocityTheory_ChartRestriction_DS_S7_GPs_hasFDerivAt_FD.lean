-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.hasFDerivAt_FD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:45.255065+00:00
-- url     : https://prove2.me/submissions/e64cf317-feed-49d1-8897-43f8f0af6ac5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_dAtW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_hasFDerivAt_slice

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
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (T : KType ε Λ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hx : emb x k ∈ Wset n) :
    HasFDerivAt (fun y : 𝕄f => g (emb y k) • Pk T k) (FD T g x k) x := by
  have h1 := ((dAtW hg hx).hasFDerivAt.comp x (hasFDerivAt_slice (toMK k, toMK k⁻¹) x)).smul_const (Pk T k)
  exact h1.differentiableAt.hasFDerivAt
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
