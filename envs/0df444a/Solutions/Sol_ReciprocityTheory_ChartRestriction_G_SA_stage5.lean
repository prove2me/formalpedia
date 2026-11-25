-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.stage5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:07:11.903926+00:00
-- url     : https://prove2.me/submissions/8d7ff47d-815a-4901-8858-182d3a58585b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_apply_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_tor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reachableFixing_add_smul_second
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_tor_mulVec


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
theorem _root_.solution {b : ι → K} (hform : b = hf σ J b f • e + hf σ J b e • f) (hα : IsUnit (hf σ J b f)) :
    Reach σ J e f a b (e + (hf σ J b b * i2) • f) := by
  have hfe := hf_fe hσ hJ he hff hef
  have hi2 := apply_half hσ hJ he hff hef hae haf hfix h2i hδ hσδ
  set α := hf σ J b f
  set β := hf σ J b e
  set ν := hf σ J b b with hνdef
  have hν : ν = α * σ β + σ α * β := by
    rw [hνdef]
    conv_lhs => rw [hform]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, he, hff, hef, hfe]
    ring
  have hσν : σ ν = ν := hf_symm hσ hJ b b
  obtain ⟨αi, hαi⟩ := hα.exists_right_inv
  have hml : σ α * σ αi = 1 := by rw [← map_mul, hαi, map_one]
  have r1 : Reach σ J e f a b (e + (σ α * β) • f) := by
    have := reach_tor hσ hJ he hff hef hae haf hml b
    have htor : tor σ J e f αi (σ α) *ᵥ b = e + (σ α * β) • f := by
      rw [tor_mulVec]
      conv_lhs => rw [hform]
      simp only [hf_add_left, hf_smul_left, hef, hff, he, hfe, mul_one, mul_zero, add_zero, zero_add]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e i * hαi
    rwa [htor] at this
  have hc : σ (ν * i2 - σ α * β) = -(ν * i2 - σ α * β) := by
    rw [map_sub, map_mul, map_mul, hσν, hi2, hσ]
    linear_combination ν * h2i + hν
  have r2 := reachableFixing_add_smul_second hσ hJ he hff hef hae haf hc (e + (σ α * β) • f)
  have hb1f : hf σ J (e + (σ α * β) • f) f = 1 := by
    simp [hf_add_left, hf_smul_left, hef, hff]
  rw [hb1f] at r2
  have heq : e + (σ α * β) • f + ((ν * i2 - σ α * β) * 1) • f = e + (ν * i2) • f := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq] at r2
  exact reach_trans hσ hJ he hff hef r1 r2
end ReciprocityTheory.ChartRestriction.G.SA
