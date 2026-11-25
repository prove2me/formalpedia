-- Prove2me | solution 1 for WhenToTrustYourModel.tvd_joint_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:41:14.7338+00:00
-- url     : https://prove2.me/submissions/40d749bf-dfde-46c3-b338-397d6103d132

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic

set_option autoImplicit false

open Finset
namespace WhenToTrustYourModel

lemma tvj_second {X Y : Type*} [Fintype X] [Fintype Y]
    (p₁ p₂ : X → ℝ) (hp₁ : IsDist p₁) (hp₂ : IsDist p₂)
    (q₁ q₂ : X → Y → ℝ) (hq₁ : ∀ x, IsDist (q₁ x)) (hq₂ : ∀ x, IsDist (q₂ x)) :
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤
      tvDist p₁ p₂ + ∑ x, p₁ x * tvDist (q₁ x) (q₂ x) := by
  unfold tvDist jointDist
  rw [Fintype.sum_prod_type]
  have key : ∀ x, ∑ y, |p₁ x * q₁ x y - p₂ x * q₂ x y| ≤
      |p₁ x - p₂ x| + p₁ x * ∑ y, |q₁ x y - q₂ x y| := by
    intro x
    have h1 : ∀ y, |p₁ x * q₁ x y - p₂ x * q₂ x y| ≤
        |p₁ x - p₂ x| * q₂ x y + p₁ x * |q₁ x y - q₂ x y| := by
      intro y
      have e : p₁ x * q₁ x y - p₂ x * q₂ x y = (p₁ x - p₂ x) * q₂ x y + p₁ x * (q₁ x y - q₂ x y) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg ((hq₂ x).1 y), abs_of_nonneg (hp₁.1 x)]
    refine (Finset.sum_le_sum (fun y _ => h1 y)).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hq₂ x).2, mul_one]
  have := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset X)) => key x)
  rw [Finset.sum_add_distrib] at this
  have e2 : ∑ x, p₁ x * (1 / 2 * ∑ y, |q₁ x y - q₂ x y|) = 1/2 * ∑ x, p₁ x * ∑ y, |q₁ x y - q₂ x y| := by
    rw [Finset.mul_sum]; congr 1; funext x; ring
  rw [e2]; linarith

theorem tvd_joint_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (p₁ p₂ : X → ℝ) (hp₁ : IsDist p₁) (hp₂ : IsDist p₂)
    (q₁ q₂ : X → Y → ℝ) (hq₁ : ∀ x, IsDist (q₁ x)) (hq₂ : ∀ x, IsDist (q₂ x)) :
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤ tvDist p₁ p₂ + (⨆ x, tvDist (q₁ x) (q₂ x)) ∧
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤
      tvDist p₁ p₂ + ∑ x, p₁ x * tvDist (q₁ x) (q₂ x) := by
  have h2 := tvj_second p₁ p₂ hp₁ hp₂ q₁ q₂ hq₁ hq₂
  refine ⟨h2.trans ?_, h2⟩
  have hb : BddAbove (Set.range fun x => tvDist (q₁ x) (q₂ x)) := (Set.finite_range _).bddAbove
  have : ∑ x, p₁ x * tvDist (q₁ x) (q₂ x) ≤ ∑ x, p₁ x * (⨆ x, tvDist (q₁ x) (q₂ x)) :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (le_ciSup hb x) (hp₁.1 x))
  rw [← Finset.sum_mul, hp₁.2, one_mul] at this
  linarith

end WhenToTrustYourModel

open WhenToTrustYourModel in
theorem solution {X Y : Type*} [Fintype X] [Fintype Y]
    (p₁ p₂ : X → ℝ) (hp₁ : IsDist p₁) (hp₂ : IsDist p₂)
    (q₁ q₂ : X → Y → ℝ) (hq₁ : ∀ x, IsDist (q₁ x)) (hq₂ : ∀ x, IsDist (q₂ x)) :
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤ tvDist p₁ p₂ + (⨆ x, tvDist (q₁ x) (q₂ x)) ∧
    tvDist (jointDist p₁ q₁) (jointDist p₂ q₂) ≤
      tvDist p₁ p₂ + ∑ x, p₁ x * tvDist (q₁ x) (q₂ x) :=
  WhenToTrustYourModel.tvd_joint_bound p₁ p₂ hp₁ hp₂ q₁ q₂ hq₁ hq₂
