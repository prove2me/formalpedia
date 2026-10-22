-- Prove2me | solution 1 for StrategicRFx.Benefit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T02:19:29.653499+00:00
-- url     : https://prove2.me/submissions/da8355f4-6d4f-4ac8-96b9-65ffd525e732

import Mathlib
import Definitions.Def_StrategicRFx_Benefit_Setting

open StrategicRFx.Benefit

lemma rfx5_key (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) :
    ∃ p1 p2 : ℝ, 0 ≤ p1 ∧ 0 ≤ p2 ∧ θ * p1 + (1 - θ) * p2 = 1 ∧ (p1 = p2 ↔ y = θ * A) ∧
      nashProduct θ y (A - y) = (p1 ^ θ * p2 ^ (1 - θ)) * nashProduct θ (θ * A) (A - θ * A) ∧
      0 < nashProduct θ (θ * A) (A - θ * A) := by
  have hθA : 0 < θ * A := mul_pos hθ0 hA
  have h1θ : 0 < 1 - θ := by linarith
  have h1θA : 0 < (1 - θ) * A := mul_pos h1θ hA
  refine ⟨y / (θ * A), (A - y) / ((1 - θ) * A), div_nonneg hy0 hθA.le,
    div_nonneg (by linarith) h1θA.le, by field_simp; ring, ?_, ?_, ?_⟩
  · rw [div_eq_div_iff hθA.ne' h1θA.ne']
    constructor
    · intro h
      have : (y - θ * A) * A = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · linarith
    · intro h; rw [h]; ring
  · unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    have ex : y = y / (θ * A) * (θ * A) := by field_simp
    have eAx : A - y = (A - y) / ((1 - θ) * A) * ((1 - θ) * A) := by field_simp
    rw [eAx]
    conv_lhs => rw [ex]
    rw [Real.mul_rpow (div_nonneg hy0 hθA.le) hθA.le,
      Real.mul_rpow (div_nonneg (by linarith) h1θA.le) h1θA.le]
    rw [← ex, ← eAx]
    ring
  · unfold nashProduct
    rw [show A - θ * A = (1 - θ) * A by ring]
    exact mul_pos (Real.rpow_pos_of_pos hθA _) (Real.rpow_pos_of_pos h1θA _)

lemma rfx5_strict (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) (hne : y ≠ θ * A) :
    nashProduct θ y (A - y) < nashProduct θ (θ * A) (A - θ * A) := by
  obtain ⟨p1, p2, hp1, hp2, hs, hiff, he, hpos⟩ := rfx5_key θ A y hθ0 hθ1 hA hy0 hyA
  have hlt := (Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos (w₂ := 1 - θ) hθ0 (by linarith) hp1 hp2
    (by ring)).2 (fun h => hne (hiff.1 h))
  rw [he]; nlinarith

lemma rfx5_max (θ A y : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA0 : 0 ≤ A) (hy0 : 0 ≤ y)
    (hyA : y ≤ A) : nashProduct θ y (A - y) ≤ nashProduct θ (θ * A) (A - θ * A) := by
  rcases eq_or_ne y (θ * A) with h | h
  · rw [h]
  rcases eq_or_lt_of_le hA0 with hA | hA
  · subst hA; exfalso; apply h; simp; linarith
  exact (rfx5_strict θ A y hθ0 hθ1 hA hy0 hyA h).le

theorem solution (P : Params) (hP : Standing P) (j : Fin 2) (πi π' : ℝ) :
    (0 ≤ P.Pi - πi - π' →
      (∀ x, IsFollowerSolution P j πi π' x ↔ x = followerSplit P j πi π') ∧
        P.Pi - πi - followerSplit P j πi π' = (1 - P.θ j) * (P.Pi - πi) + P.θ j * π') ∧
    (P.Pi - πi - π' < 0 → ∀ x, ¬ IsFollowerSolution P j πi π' x) := by
  have hθ0 := hP.θ_pos j
  have hθ1 := hP.θ_lt_one j
  refine ⟨fun hA0 => ⟨fun x => ?_, by unfold followerSplit; ring⟩, ?_⟩
  · set A := P.Pi - πi - π' with hA
    have e : ∀ z, P.Pi - πi - z - π' = A - z := fun z => by rw [hA]; ring
    have hfs : followerSplit P j πi π' = P.θ j * A := rfl
    rw [hfs]
    constructor
    · rintro ⟨⟨hx0, hxA⟩, hmax⟩
      by_contra hne
      have hxA' : x ≤ A := by linarith
      rcases eq_or_lt_of_le hA0 with hA' | hA'
      · apply hne; rw [← hA'] at hxA' ⊢; simp; linarith
      have h1 := rfx5_strict (P.θ j) A x hθ0 hθ1 hA' hx0 hxA' hne
      have h2 := hmax (P.θ j * A) ⟨mul_nonneg hθ0.le hA0, by nlinarith⟩
      rw [e, e] at h2
      linarith
    · rintro rfl
      refine ⟨⟨mul_nonneg hθ0.le hA0, by nlinarith⟩, fun y hy => ?_⟩
      rw [e, e]
      exact rfx5_max (P.θ j) A y hθ0 hθ1 hA0 hy.1 (by linarith [hy.2])
  · intro hneg x hx
    obtain ⟨⟨hx0, hxA⟩, _⟩ := hx
    linarith
