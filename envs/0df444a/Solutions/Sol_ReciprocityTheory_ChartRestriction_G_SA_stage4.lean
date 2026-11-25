-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.stage4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:39:44.281288+00:00
-- url     : https://prove2.me/submissions/50bd78b9-0476-496e-b160-6a0782a235d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_ef_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_gp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reachableFixing_add_smul_first


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
theorem _root_.solution {b : ι → K} (hform : b = hf σ J b f • e + hf σ J b e • f)
    (hcop : IsCoprime (hf σ J b f) (hf σ J b e)) :
    ∃ b', Reach σ J e f a b b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧ IsUnit (hf σ J b' f) := by
  have h2 : IsUnit (2 : K) := ⟨⟨2, i2, h2i, by rw [mul_comm]; exact h2i⟩, rfl⟩
  set α := hf σ J b f
  set β := hf σ J b e
  have hval := fun x y => hf_ef_left hσ hJ he hff hef (e := e) (f := f) x y
  rcases gp hσ hfix h2 hδ hσδ hcop with h | h | h
  · exact ⟨b, reach_refl hσ hJ he hff hef b, hform, h⟩
  · have hb' : b + (δ * β) • e = (α + δ * β) • e + β • f := by rw [hform]; module
    refine ⟨_, reachableFixing_add_smul_first hσ hJ he hff hef hae haf hσδ b, ?_, ?_⟩
    · rw [hb', (hval _ _).1, (hval _ _).2]
    · rw [hb', (hval _ _).2]; exact h
  · have hb' : b + (-1 * δ * β) • e = (α + -1 * δ * β) • e + β • f := by rw [hform]; module
    refine ⟨_, reachableFixing_add_smul_first hσ hJ he hff hef hae haf (c := -1 * δ) (by rw [map_mul, hσδ]; simp) b, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc (-1) δ] at hb' ⊢
      rw [hb', (hval _ _).1, (hval _ _).2]
    · rw [mul_assoc, ← mul_assoc (-1) δ] at hb' ⊢
      rw [hb', (hval _ _).2]; exact h
end ReciprocityTheory.ChartRestriction.G.SA
