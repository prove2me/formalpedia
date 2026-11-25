-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:29.010377+00:00
-- url     : https://prove2.me/submissions/8e75b178-a8f6-4985-9fc2-87518e0a429d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_apply
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_mulVec
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_iso_of_hf
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKG.Tow.Levi
open Matrix
variable {n : Type} [Fintype n] [DecidableEq n]
variable {M θ : Matrix n n ℂ}
namespace PositivityTheory.ThKG.Tow.Levi
theorem _root_.solution (hM : ∀ i j, star (M j i) = M i j) (h1 : θ * θ = 1) (h2 : θᵀ * M * θ.map star = M)
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {u u' : n → ℂ}
    (hu : θ *ᵥ u = ε • u) (hu' : θ *ᵥ u' = ε • u') (e : hf M u u = hf M u' u') :
    ∃ κ : Matrix n n ℂ, κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ u = u' ∧ ∀ z, θ *ᵥ z = -ε • z → κ *ᵥ z = z := by
  obtain ⟨a, ha⟩ : ∃ a, a = u - u' := ⟨_, rfl⟩
  have hθ : ∀ x y, hf M (θ *ᵥ x) (θ *ᵥ y) = hf M x y := fun x y => by rw [hf_mulVec, h2]
  have hθθ : ∀ x, θ *ᵥ (θ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h1, one_mulVec]
  have hεc : starRingEnd ℂ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hθa : θ *ᵥ a = ε • a := by rw [ha, mulVec_sub, hu, hu', smul_sub]
  have haa : hf M a a = hf M u a + starRingEnd ℂ (hf M u a) := by
    rw [hf_conj hM, ha]
    simp only [map_sub, LinearMap.sub_apply]
    rw [e]; ring
  obtain ⟨b, hb⟩ : ∃ b, b = hf M u a := ⟨_, rfl⟩
  rw [← hb] at haa
  let κ : Matrix n n ℂ := 1 - b⁻¹ • vecMulVec a (M *ᵥ star a)
  have hκ : ∀ z, κ *ᵥ z = z - (b⁻¹ * hf M z a) • a := fun z => by
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hf_apply, dotProduct_comm z]
    simp [mul_smul]
  refine ⟨κ, iso_of_hf fun z w => ?_, ?_, ?_, fun z hz => ?_⟩
  · rw [hκ, hκ]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, haa,
      map_mul, map_inv₀, hf_conj hM]
    by_cases h0 : b = 0
    · simp [h0]
    · have h0' : starRingEnd ℂ b ≠ 0 := by simpa using h0
      field_simp
      ring
  · refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
    have : hf M (θ *ᵥ z) a = ε * hf M z a := by
      rw [← hθ, hθθ, hθa, LinearMap.map_smulₛₗ, hεc, smul_eq_mul]
    rw [toLin'_apply, toLin'_apply, ← mulVec_mulVec, ← mulVec_mulVec, hκ, hκ, mulVec_sub, mulVec_smul, hθa, this, smul_smul]
    congr 2
    ring
  · rw [hκ, ← hb]
    by_cases h0 : b = 0
    · have : a = 0 := by
        by_contra hne
        have := h3 a hne
        rw [hθa, map_smul, LinearMap.smul_apply, haa, h0] at this
        simp at this
      rw [this, smul_zero, sub_zero]
      exact sub_eq_zero.1 (ha ▸ this)
    · rw [inv_mul_cancel₀ h0, one_smul, ha, sub_sub_cancel]
  · have : hf M z a = 0 := by
      have := hθ z a
      rw [hz, hθa, LinearMap.map_smulₛₗ, hεc, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at this
      linear_combination (-1 / 2 : ℂ) * this - (1 / 2 : ℂ) * hf M z a * hεε
    rw [hκ, this, mul_zero, zero_smul, sub_zero]
end PositivityTheory.ThKG.Tow.Levi
