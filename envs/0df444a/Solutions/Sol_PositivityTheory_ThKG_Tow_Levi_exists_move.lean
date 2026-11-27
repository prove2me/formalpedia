-- Prove2me | solution 1 for PositivityTheory.ThKG.Tow.Levi.exists_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:29.399047+00:00
-- url     : https://prove2.me/submissions/092ef4f7-f17f-4edf-b87e-5281ce04e0bb

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_TowerModels_ExistsRefl
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_mulVec
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_iso_of_hf
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_hf_conj
import Theorems.Thm_PositivityTheory_ThKG_Tow_Levi_exists_refl

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
    (h3 : ∀ x : n → ℂ, x ≠ 0 → 0 < (hf M (θ *ᵥ x) x).re) {v v' : n → ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0)
    (e : hf M v v = 0) (e' : hf M v' v' = 0) :
    ∃ (κ : Matrix n n ℂ) (t : ℂ), t ≠ 0 ∧ κᵀ * M * κ.map star = M ∧ Commute κ θ ∧ κ *ᵥ v = t • v' := by
  have hθ : ∀ x y, hf M (θ *ᵥ x) (θ *ᵥ y) = hf M x y := fun x y => by rw [hf_mulVec, h2]
  have hθθ : ∀ x, θ *ᵥ (θ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, h1, one_mulVec]
  have hs : ∀ x, hf M x (θ *ᵥ x) = hf M (θ *ᵥ x) x := fun x => by rw [← hθ, hθθ]
  have hre : ∀ x, ((hf M (θ *ᵥ x) x).re : ℂ) = hf M (θ *ᵥ x) x := fun x =>
    Complex.conj_eq_iff_re.1 (by rw [hf_conj hM, hs])
  have p := h3 v hv
  have p' := h3 v' hv'
  let t : ℝ := Real.sqrt ((hf M (θ *ᵥ v) v).re / (hf M (θ *ᵥ v') v').re)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos p p')
  have htt : (t : ℂ) * t * hf M (θ *ᵥ v') v' = hf M (θ *ᵥ v) v := by
    rw [← hre v, ← hre v', ← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt (div_pos p p').le,
      div_mul_cancel₀ _ p'.ne']
  obtain ⟨w, hw⟩ : ∃ w, w = (t : ℂ) • v' := ⟨_, rfl⟩
  have ew : hf M w w = 0 := by
    rw [hw, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, e', smul_zero, smul_zero]
  have ew' : hf M (θ *ᵥ w) w = hf M (θ *ᵥ v) v := by
    rw [hw, LinearMap.map_smulₛₗ, mulVec_smul, map_smul, LinearMap.smul_apply, Complex.conj_ofReal, ← htt, smul_eq_mul,
      smul_eq_mul, mul_assoc]
  have ep : ∀ x, θ *ᵥ (x + θ *ᵥ x) = (1 : ℂ) • (x + θ *ᵥ x) := fun x => by rw [mulVec_add, hθθ, one_smul, add_comm]
  have em : ∀ x, θ *ᵥ (x - θ *ᵥ x) = (-1 : ℂ) • (x - θ *ᵥ x) := fun x => by rw [mulVec_sub, hθθ, neg_one_smul, neg_sub]
  obtain ⟨κ₁, a1, a2, a3, a4⟩ := exists_refl hM h1 h2 h3 (Or.inl rfl) (ep v) (ep w) (by
    simp only [map_add, LinearMap.add_apply, hθ, hs, e, ew, ew'])
  obtain ⟨κ₂, b1, b2, b3, b4⟩ := exists_refl hM h1 h2 h3 (Or.inr rfl) (em v) (em w) (by
    simp only [map_sub, LinearMap.sub_apply, hθ, hs, e, ew, ew'])
  refine ⟨κ₂ * κ₁, t, by exact_mod_cast ht.ne', iso_of_hf fun x y => ?_, b2.mul_left a2, ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hf_mulVec, b1, hf_mulVec, a1]
  · have e1 : v = (2 : ℂ)⁻¹ • ((v + θ *ᵥ v) + (v - θ *ᵥ v)) := by module
    rw [← hw, ← mulVec_mulVec, e1, mulVec_smul, mulVec_add, a3, a4 _ (em v), mulVec_smul, mulVec_add, b3,
      b4 _ (by rw [neg_neg]; exact ep w)]
    module
end PositivityTheory.ThKG.Tow.Levi
