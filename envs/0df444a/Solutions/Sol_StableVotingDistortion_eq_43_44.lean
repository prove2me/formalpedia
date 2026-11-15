-- Prove2me | solution 1 for StableVotingDistortion.eq_43_44
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T12:00:19.29903+00:00
-- url     : https://prove2.me/submissions/2ed9a97f-4b48-44cd-9bd1-51318cab3029

import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Mathlib

-- Source module PrimitiveBounds
section
set_option autoImplicit true
namespace StableVotingDistortion
open Set MeasureTheory

theorem primitive_sandwich {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b-a)*ϕ b ≤ J ϕ b - J ϕ a ∧ J ϕ b - J ϕ a ≤ (b-a)*ϕ a := by
  have hi {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : IntervalIntegrable ϕ volume x y :=
    (h.continuousOn.mono (Icc_subset_Icc hx hy)).intervalIntegrable_of_Icc hxy
  have hdiff : J ϕ b - J ϕ a = ∫ r in a..b, ϕ r := by
    have hs := intervalIntegral.integral_add_adjacent_intervals (hi (le_refl 0) ha (hab.trans hb)) (hi ha hab hb)
    unfold J
    linarith
  rw [hdiff]
  have hlow := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := ϕ b)) (hi ha hab hb)
    (fun r hr => h.antitoneOn ⟨ha.trans hr.1, hr.2.trans hb⟩ ⟨ha.trans hab, hb⟩ hr.2)
  have hhi := intervalIntegral.integral_mono_on hab (hi ha hab hb) (intervalIntegrable_const (c := ϕ a))
    (fun r hr => h.antitoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hr.1, hr.2.trans hb⟩ hr.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using And.intro hlow hhi

theorem eq_43_44 {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ) :
    (∀ p q, 0 ≤ q → q ≤ p → p ≤ 1 →
      deltaP ϕ p q ≤ p - q ∧ deltaP ϕ p q ≤ (1 - p) * ϕ q ∧ q * ϕ q ≤ J ϕ q) ∧
      ∀ p q z, 0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 → KP ϕ p q z ≤ -(p - q) * ϕ z - J ϕ q := by
  have h0 : J ϕ 0 = 0 := by simp [J]
  have h1 : J ϕ 1 = 0 := hϕ.integral_eq_zero
  have hleft (r : ℝ) (hr : r ∈ Icc 0 1) := (primitive_sandwich hϕ (le_refl 0) hr.1 hr.2).1
  have hright (r : ℝ) (hr : r ∈ Icc 0 1) := primitive_sandwich hϕ hr.1 hr.2 (le_refl 1)
  simp only [h0,h1,hϕ.at_one,sub_zero,zero_sub] at hleft hright
  have hJ (r : ℝ) (hr : r ∈ Icc 0 1) : 0 ≤ J ϕ r := by
    by_cases hp : 0 ≤ ϕ r
    · exact (mul_nonneg hr.1 hp).trans (hleft r hr)
    · have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hr.2) (le_of_not_ge hp)
      linarith [(hright r hr).2]
  constructor
  · intro p q hq hqp hp
    let r := 1-p+q
    have hr : r ∈ Icc 0 1 := ⟨by dsimp [r]; linarith,by dsimp [r]; linarith⟩
    have hs := primitive_sandwich hϕ hq (show q≤r by dsimp [r]; linarith) hr.2
    have he : r-q=1-p := by dsimp [r]; ring
    rw [he] at hs
    change J ϕ r - J ϕ q ≤ _ ∧ J ϕ r - J ϕ q ≤ _ ∧ _
    refine ⟨?_,hs.2,hleft q ⟨hq,hqp.trans hp⟩⟩
    have hh := (hright r hr).1
    dsimp [r] at hh ⊢
    linarith [hJ q ⟨hq,hqp.trans hp⟩]
  · intro p q z hq hqp hpz hz
    have h := (primitive_sandwich hϕ (show 0≤z-p+q by linarith) (show z-p+q≤z by linarith) hz).1
    have he : z-(z-p+q)=p-q := by ring
    rw [he] at h
    unfold KP
    linarith

end StableVotingDistortion
end


open StableVotingDistortion

theorem solution :
    ∀ {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ),
    (∀ p q, 0 ≤ q → q ≤ p → p ≤ 1 →
      deltaP ϕ p q ≤ p - q ∧ deltaP ϕ p q ≤ (1 - p) * ϕ q ∧ q * ϕ q ≤ J ϕ q) ∧
      ∀ p q z, 0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 → KP ϕ p q z ≤ -(p - q) * ϕ z - J ϕ q :=
  @StableVotingDistortion.eq_43_44
