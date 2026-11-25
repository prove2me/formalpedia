-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GRPf.pair_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:29.244351+00:00
-- url     : https://prove2.me/submissions/d286f931-1d17-411a-a59d-0a6d4522e209

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_pair_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_either
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_cc_cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]
variable {T : Type} (χ : T → O →+* k) (cc : T → T) (hcc : ∀ σ a, χ (cc σ) a = χ σ (star a))
  (hunit : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
include hunit
include hcc
namespace ReciprocityTheory.ChartRestriction.G.TB.GRPf
theorem _root_.solution {c : k} (hc : c ≠ 0) (σ σ' : T)
    (h : ∀ a, c * (χ σ a * χ σ (star a) + χ σ' a * χ σ' (star a) - 2 * χ σ a * χ σ' a) = 0) : σ' = cc σ := by
  have P1 : ∀ a, c * ((χ σ a - χ (cc σ) a) * (χ σ a - χ (cc σ') a)) = 0 := by
    intro a
    rw [hcc, hcc]
    exact pair_prod c (χ σ) (χ σ') h a
  have h' : ∀ a, c * (χ σ' a * χ σ' (star a) + χ σ a * χ σ (star a) - 2 * χ σ' a * χ σ a) = 0 := by
    intro a
    linear_combination h a
  have P2 : ∀ a, c * ((χ σ' a - χ (cc σ') a) * (χ σ' a - χ (cc σ) a)) = 0 := by
    intro a
    rw [hcc, hcc]
    exact pair_prod c (χ σ') (χ σ) h' a
  rcases either χ hunit hc σ _ _ P1 with h1 | h1
  · rcases either χ hunit hc σ' _ _ P2 with h2 | h2
    · by_contra hne
      have hne' : σ ≠ σ' := fun e => hne (by rw [← e]; exact h1)
      obtain ⟨a, ha⟩ := hunit σ σ' hne'
      have hs : χ σ (star a) = χ σ a := by rw [← hcc, ← h1]
      have hs' : χ σ' (star a) = χ σ' a := by rw [← hcc, ← h2]
      have e := h a
      rw [hs, hs'] at e
      have e' : ((χ σ a - χ σ' a) * (χ σ a - χ σ' a)) * c = 0 := by linear_combination e
      exact hc ((ha.mul ha).mul_right_eq_zero.1 e')
    · exact h2
  · rw [h1, cc_cc χ cc hcc hunit hc]
end ReciprocityTheory.ChartRestriction.G.TB.GRPf
