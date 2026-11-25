-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inner_actM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:57.112488+00:00
-- url     : https://prove2.me/submissions/64c12d5a-202e-46e3-a41e-b4fcf63e9474

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_add__8c46905f3067
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_actM_smul__ee45d6d95b18
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inner_actM_add_inner_actM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inG_sub_theta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_inG_add_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (M : Matrix (Fin n) (Fin n) ℂ) (x y : D) :
    inner ℂ (actM E M x) y = inner ℂ x (actM E (Jm ε * Mᴴ * Jm ε) y) := by
  have skA := inner_actM_add_inner_actM hσ hD (inG_sub_theta ε M) x y
  have skB := inner_actM_add_inner_actM hσ hD (inG_add_theta ε M) x y
  have hc : Complex.I / 2 * -Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, mul_neg, Complex.I_mul_I]
    norm_num
  have hM : M = (1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  have hT : Jm ε * Mᴴ * Jm ε = (-(1 / 2) : ℂ) • (M - Jm ε * Mᴴ * Jm ε) +
      (Complex.I / 2) • ((-Complex.I) • (M + Jm ε * Mᴴ * Jm ε)) := by
    rw [smul_smul, hc]
    first
      | module
      | (ext i j; simp; ring)
  rw [hT]
  conv_lhs => rw [hM]
  rw [actM_add', actM_add', actM_smul' E (1 / 2 : ℂ), actM_smul' E (-(1 / 2) : ℂ),
    actM_smul' E (Complex.I / 2)]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_div₀, map_one, map_ofNat, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * skA - (Complex.I / 2) * skB
end ReciprocityTheory.ChartRestriction.DS
