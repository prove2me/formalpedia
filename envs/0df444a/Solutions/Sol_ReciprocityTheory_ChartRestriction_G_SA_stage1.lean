-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.stage1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:57.059993+00:00
-- url     : https://prove2.me/submissions/13e9f145-598b-4a6a-8614-e565c4c2042f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_decomp_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_apply_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_eich_e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_stepA


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
theorem _root_.solution (hmax : ∀ m₀ m₁ m₂ : Ideal K, m₀.IsMaximal → m₁.IsMaximal → m₂.IsMaximal →
      m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂)
    {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hν : IsUnit (hf σ J b b)) :
    ∃ b', Reach σ J e f a b b' ∧ IsCoprime (hf σ J b' f) (hf σ J b' e) := by
  have h2 : IsUnit (2 : K) := ⟨⟨2, i2, h2i, by rw [mul_comm]; exact h2i⟩, rfl⟩
  have hi2 := apply_half hσ hJ he hff hef hae haf hfix h2i hδ hσδ
  have hfe := hf_fe hσ hJ he hff hef
  by_cases hcop : IsCoprime (hf σ J b f) (hf σ J b e)
  · exact ⟨b, reach_refl hσ hJ he hff hef b, hcop⟩
  obtain ⟨hwe, hwf⟩ := decomp hσ hJ he hff hef b
  set α := hf σ J b f
  set β := hf σ J b e
  set w := b - α • e - β • f with hw
  have hew : hf σ J e w = 0 := by rw [← hf_symm hσ hJ, hwe, map_zero]
  have hfw : hf σ J f w = 0 := by rw [← hf_symm hσ hJ, hwf, map_zero]
  have hea : ∀ j, hf σ J e (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, hae, map_zero]
  have hfa : ∀ j, hf σ J f (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, haf, map_zero]
  have hwa : ∀ j, hf σ J w (a j) = 0 := fun j => by
    rw [hw, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hb, hea, hfa]; ring
  have hbw : b = α • e + β • f + w := by rw [hw]; abel
  obtain ⟨ω, hω⟩ : ∃ ω, ω = hf σ J w w := ⟨_, rfl⟩
  have hdef : hf σ J b b = α * σ β + σ α * β + ω := by
    rw [hω]
    conv_lhs => rw [hbw]
    exact hf_decomp_self hσ hJ he hff hef α β hwe hwf
  have hbwv : hf σ J b w = ω := by
    have h1 : hf σ J b w = α * hf σ J e w + β * hf σ J f w + hf σ J w w := by
      conv_lhs => rw [hbw]
      simp only [hf_add_left, hf_smul_left]
    rw [h1, hew, hfw, hω]; ring
  set c := -(ω * i2)
  have hσω : σ ω = ω := by rw [hω]; exact hf_symm hσ hJ w w
  have smove : ∀ sg : K, σ sg = sg → sg * sg = 1 →
      Reach σ J e f a b (eich σ J e (sg • w) c *ᵥ b) ∧
        hf σ J (eich σ J e (sg • w) c *ᵥ b) f = α - sg * ω + c * β ∧
        hf σ J (eich σ J e (sg • w) c *ᵥ b) e = β := by
    intro sg hs1 hs2
    refine ⟨reach_eich_e hσ hJ he hff hef hae haf (by simp [hf_smul_left, hwe])
      (by simp [hf_smul_left, hwf]) ?_ (fun j => by simp [hf_smul_left, hwa]) b, ?_, ?_⟩
    · simp only [c, hf_smul_left, hf_smul_right, hs1, map_neg, map_mul, hσω, hi2, ← hω]
      linear_combination (-ω) * h2i + ω * hs2
    · rw [eich_mulVec]
      simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hwf, hef, hbwv, hs1]
      ring
    · rw [eich_mulVec]
      simp only [hf_add_left, hf_sub_left, hf_smul_left, hf_smul_right, hwe, he]
      ring
  rcases stepA hmax h2 hν hdef hcop (c := c) with h | h
  · obtain ⟨r, h1, h3⟩ := smove 1 (map_one σ) (one_mul 1)
    refine ⟨_, r, ?_⟩
    rw [h1, h3, one_mul]; exact h
  · obtain ⟨r, h1, h3⟩ := smove (-1) (by rw [map_neg, map_one]) (by ring)
    refine ⟨_, r, ?_⟩
    rw [h1, h3, show α - -1 * ω + c * β = α + ω + c * β by ring]; exact h
end ReciprocityTheory.ChartRestriction.G.SA
