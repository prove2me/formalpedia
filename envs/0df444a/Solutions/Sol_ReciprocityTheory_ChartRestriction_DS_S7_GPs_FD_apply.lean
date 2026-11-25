-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.FD_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:05:57.6698+00:00
-- url     : https://prove2.me/submissions/a5d22f2d-92a1-4c6c-9c48-c0a00d905336

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_dAtW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_zeroEmbedding_apply
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
    (hg : ContDiffOn ℂ ∞ g (Wset n)) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hx : emb x k ∈ Wset n)
    (H : Matrix (Fin n) (Fin n) ℂ) : FD T g x k H = fderiv ℂ g (emb x k) (H, 0) • Pk T k := by
  have h1 := ((dAtW hg hx).hasFDerivAt.comp x (hasFDerivAt_slice (toMK k, toMK k⁻¹) x)).smul_const (Pk T k)
  have h2 : FD T g x k = ((fderiv ℂ g (emb x k)).comp (I0 n)).smulRight (Pk T k) := h1.fderiv
  have h3 : ∀ v : Matrix (Fin n) (Fin n) ℂ, ((fderiv ℂ g (emb x k)).comp (I0 n)).smulRight (Pk T k) v =
      fderiv ℂ g (emb x k) (v, 0) • Pk T k := fun v => by
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, zeroEmbedding_apply]
  rw [h2]
  exact h3 H
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
