-- Prove2me | solution 1 for TheoryOfGames.Utility.normalized_utility_affine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:48:39.199498+00:00
-- url     : https://prove2.me/submissions/5e24d9fd-1af0-40c0-aa47-9c66e7337a86

import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

set_option autoImplicit false

namespace P2M20e72de8

open TheoryOfGames.Utility

lemma oneSub_oneSub (b : OpenUnit) : OpenUnit.oneSub (OpenUnit.oneSub b) = b := by
  apply Subtype.ext
  simp [OpenUnit.oneSub]

lemma mul_comm' (a b : OpenUnit) : OpenUnit.mul a b = OpenUnit.mul b a := by
  apply Subtype.ext
  simp [OpenUnit.mul, mul_comm]

/-- `h (mix b w u) = h u + b (h w - h u)` whenever `w ≠ u` (via (iv) in either order). -/
lemma mix_val {U : Type*} (S : UtilitySystem U) (h : U → ℝ)
    (hiv : ∀ (γ : OpenUnit) (u v : U), S.lt u v →
      h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v)
    (b : OpenUnit) (w u : U) (hne : h w ≠ h u) :
    h (S.mix b w u) = h u + (b : ℝ) * (h w - h u) := by
  rcases S.complete w u with ⟨heq, -, -⟩ | ⟨hgt, -, -⟩ | ⟨hgt, -, -⟩
  · exact absurd (congrArg h heq) hne
  · -- u < w
    have e := hiv b u w hgt
    have hc : S.cmb b u w = S.mix b w u := by
      unfold UtilitySystem.cmb
      rw [S.mix_comm, oneSub_oneSub]
    rw [hc] at e
    rw [e]; ring
  · -- w < u
    have e := hiv (OpenUnit.oneSub b) w u hgt
    have hc : S.cmb (OpenUnit.oneSub b) w u = S.mix b w u := by
      unfold UtilitySystem.cmb
      rw [oneSub_oneSub]
    rw [hc] at e
    rw [e]
    simp only [OpenUnit.oneSub]
    ring

lemma d_scale {U : Type*} (S : UtilitySystem U) (h : U → ℝ)
    (hiv : ∀ (γ : OpenUnit) (u v : U), S.lt u v →
      h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v)
    (a b : OpenUnit) (u : U) (hne : h (S.mix a u u) ≠ h u) :
    h (S.mix (OpenUnit.mul b a) u u) = h u + (b : ℝ) * (h (S.mix a u u) - h u) := by
  rw [← S.mix_mix]
  exact mix_val S h hiv b _ u hne

lemma d_half {U : Type*} (S : UtilitySystem U) (h : U → ℝ)
    (hiv : ∀ (γ : OpenUnit) (u v : U), S.lt u v →
      h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v)
    (a : OpenUnit) (u : U) (hne : h (S.mix a u u) ≠ h u) : (a : ℝ) = 1 / 2 := by
  have hsym : S.mix (OpenUnit.oneSub a) u u = S.mix a u u := (S.mix_comm a u u).symm
  have hne' : h (S.mix (OpenUnit.oneSub a) u u) ≠ h u := by rw [hsym]; exact hne
  have e1 := d_scale S h hiv a (OpenUnit.oneSub a) u hne
  have e2 := d_scale S h hiv (OpenUnit.oneSub a) a u hne'
  rw [hsym, mul_comm' a (OpenUnit.oneSub a)] at e2
  rw [e1] at e2
  have hd : h (S.mix a u u) - h u ≠ 0 := sub_ne_zero.mpr hne
  have : ((OpenUnit.oneSub a : OpenUnit) : ℝ) = (a : ℝ) := by
    apply mul_right_cancel₀ hd
    linarith
  simp only [OpenUnit.oneSub] at this
  linarith

lemma d_zero {U : Type*} (S : UtilitySystem U) (h : U → ℝ)
    (hiv : ∀ (γ : OpenUnit) (u v : U), S.lt u v →
      h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v)
    (a : OpenUnit) (u : U) : h (S.mix a u u) = h u := by
  by_contra hne
  have ha := d_half S h hiv a u hne
  have e := d_scale S h hiv a a u hne
  have hd : h (S.mix a u u) - h u ≠ 0 := sub_ne_zero.mpr hne
  have hne2 : h (S.mix (OpenUnit.mul a a) u u) ≠ h u := by
    rw [e]
    intro h0
    have : (a : ℝ) * (h (S.mix a u u) - h u) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · rw [ha] at h1; norm_num at h1
    · exact hd h1
  have ha2 := d_half S h hiv _ u hne2
  simp only [OpenUnit.mul] at ha2
  rw [ha] at ha2
  norm_num at ha2

end P2M20e72de8

open TheoryOfGames.Utility in
theorem solution {U : Type*} (S : UtilitySystem U) {uStar vStar : U}
    (hStar : S.lt uStar vStar) (h : U → ℝ) (hi : h uStar = 0) (hii : h vStar = 1)
    (hiii : ∀ u v : U, S.lt u v → h u < h v)
    (hiv : ∀ (γ : OpenUnit) (u v : U), S.lt u v →
      h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v) :
    ∀ (γ : OpenUnit) (u v : U), h (S.cmb γ u v) = (1 - (γ : ℝ)) * h u + (γ : ℝ) * h v := by
  intro γ u v
  rcases S.complete u v with ⟨heq, -, -⟩ | ⟨hgt, -, -⟩ | ⟨hgt, -, -⟩
  · subst heq
    unfold UtilitySystem.cmb
    rw [P2M20e72de8.d_zero S h hiv]
    ring
  · -- v < u
    have e := hiv (OpenUnit.oneSub γ) v u hgt
    have hc : S.cmb (OpenUnit.oneSub γ) v u = S.cmb γ u v := by
      unfold UtilitySystem.cmb
      rw [S.mix_comm (OpenUnit.oneSub γ) u v]
    rw [hc] at e
    rw [e]
    simp only [OpenUnit.oneSub]
    ring
  · exact hiv γ u v hgt
