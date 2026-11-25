-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.stage2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:37.140129+00:00
-- url     : https://prove2.me/submissions/4b504e35-7290-45d5-9cd1-ea0e388abce1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_gp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_neg_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reachableFixing_add_smul_second


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
include hσ hJ he hff hef hae haf hfix h2i hδ hσδ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {b : ι → K} (hcop : IsCoprime (hf σ J b f) (hf σ J b e)) :
    ∃ b', Reach σ J e f a b b' ∧ IsUnit (hf σ J b' e) := by
  have hfe := hf_fe hσ hJ he hff hef
  have h2 : IsUnit (2 : K) := ⟨⟨2, i2, h2i, by rw [mul_comm]; exact h2i⟩, rfl⟩
  rcases gp hσ hfix h2 hδ hσδ hcop.symm with h | h | h
  · exact ⟨b, reach_refl hσ hJ he hff hef b, h⟩
  · refine ⟨_, reachableFixing_add_smul_second hσ hJ he hff hef hae haf hσδ b, ?_⟩
    simpa [hf_add_left, hf_smul_left, hfe] using h
  · refine ⟨_, reachableFixing_add_smul_second hσ hJ he hff hef hae haf (c := -1 * δ) (by rw [map_mul, hσδ]; simp) b, ?_⟩
    simpa [hf_add_left, hf_smul_left, hf_neg_left, neg_smul, hfe, mul_assoc] using h
end ReciprocityTheory.ChartRestriction.G.SA
