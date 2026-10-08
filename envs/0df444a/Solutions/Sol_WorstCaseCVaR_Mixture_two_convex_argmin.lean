-- Prove2me | solution 1 for WorstCaseCVaR.Mixture.two_convex_argmin
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T04:31:18.431294+00:00
-- url     : https://prove2.me/submissions/30c5c28f-981f-4dd0-9e6c-73c85b4e6541

import Mathlib

section
set_option autoImplicit false
namespace MixtureCodex

lemma convex_strict_combo (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (t z r u v : ℝ) (hu : 0 ≤ u) (hv : 0 < v) (hs : u+v=1)
    (hr : u*t+v*z=r) (hz : g z < g t) : g r < g t := by
  have hc := hg.2 (Set.mem_univ t) (Set.mem_univ z) hu hv.le hs
  simp only [smul_eq_mul] at hc
  rw [hr] at hc
  have he : u*g t+v*g t = g t := by
    calc
      _ = (u+v)*g t := by ring
      _ = _ := by rw [hs,one_mul]
  have hl : u*g t+v*g z < u*g t+v*g t := by
    nlinarith [mul_pos hv (sub_pos.mpr hz)]
  rw [he] at hl
  exact hc.trans_lt hl

lemma convex_left_decrease (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (a b : ℝ) (hab : a ≤ b)
    (hm : {q : ℝ | IsMinOn g Set.univ q} = Set.Icc a b)
    (t r : ℝ) (htr : t < r) (hra : r ≤ a) : g r < g t := by
  have hmin : IsMinOn g Set.univ a := by
    change a ∈ {q : ℝ | IsMinOn g Set.univ q}
    rw [hm]
    exact ⟨le_rfl,hab⟩
  have hn : ¬ IsMinOn g Set.univ t := by
    intro ht
    have hh : t ∈ Set.Icc a b := by rw [← hm]; exact ht
    linarith [hh.1]
  have hval : g a < g t := by
    have hle := isMinOn_iff.mp hmin t (Set.mem_univ t)
    by_contra hlt
    have he := le_antisymm hle (le_of_not_gt hlt)
    apply hn
    apply isMinOn_iff.mpr
    intro q hq
    rw [← he]
    exact isMinOn_iff.mp hmin q hq
  have hd : 0 < a-t := by linarith
  let u := (a-r)/(a-t)
  let v := (r-t)/(a-t)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hra) hd.le
  have hv : 0 < v := div_pos (sub_pos.mpr htr) hd
  have hs : u+v=1 := by dsimp [u,v]; field_simp; ring
  have hp : u*t+v*a=r := by dsimp [u,v]; field_simp; ring
  exact convex_strict_combo g hg t a r u v hu hv hs hp hval

lemma convex_right_increase (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (a b : ℝ) (hab : a ≤ b)
    (hm : {q : ℝ | IsMinOn g Set.univ q} = Set.Icc a b)
    (r t : ℝ) (hbr : b ≤ r) (hrt : r < t) : g r < g t := by
  have hmin : IsMinOn g Set.univ b := by
    change b ∈ {q : ℝ | IsMinOn g Set.univ q}
    rw [hm]
    exact ⟨hab,le_rfl⟩
  have hn : ¬ IsMinOn g Set.univ t := by
    intro ht
    have hh : t ∈ Set.Icc a b := by rw [← hm]; exact ht
    linarith [hh.2]
  have hval : g b < g t := by
    have hle := isMinOn_iff.mp hmin t (Set.mem_univ t)
    by_contra hlt
    have he := le_antisymm hle (le_of_not_gt hlt)
    apply hn
    apply isMinOn_iff.mpr
    intro q hq
    rw [← he]
    exact isMinOn_iff.mp hmin q hq
  have hd : 0 < t-b := by linarith
  let u := (r-b)/(t-b)
  let v := (t-r)/(t-b)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hbr) hd.le
  have hv : 0 < v := div_pos (sub_pos.mpr hrt) hd
  have hs : u+v=1 := by dsimp [u,v]; field_simp; ring
  have hp : u*t+v*b=r := by dsimp [u,v]; field_simp; ring
  exact convex_strict_combo g hg t b r u v hu hv hs hp hval

end MixtureCodex

end


section
set_option autoImplicit false
open MeasureTheory
namespace MixtureCodex

theorem two_convex_argmin (g₁ g₂ : ℝ → ℝ)
    (hg₁ : ConvexOn ℝ Set.univ g₁) (hg₂ : ConvexOn ℝ Set.univ g₂)
    (a₁ b₁ a₂ b₂ : ℝ) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hmin₁ : {t : ℝ | IsMinOn g₁ Set.univ t} = Set.Icc a₁ b₁)
    (hmin₂ : {t : ℝ | IsMinOn g₂ Set.univ t} = Set.Icc a₂ b₂)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ + c₂) :
    ConvexOn ℝ Set.univ (fun t => c₁ * g₁ t + c₂ * g₂ t) ∧
      {t : ℝ | IsMinOn (fun t => c₁ * g₁ t + c₂ * g₂ t) Set.univ t} ⊆
        Set.Icc (min a₁ a₂) (max b₁ b₂) := by
  have hstrict {r t : ℝ} (h₁ : g₁ r < g₁ t) (h₂ : g₂ r < g₂ t) :
      c₁ * g₁ r + c₂ * g₂ r < c₁ * g₁ t + c₂ * g₂ t := by
    have hle₁ := mul_le_mul_of_nonneg_left h₁.le hc₁
    have hle₂ := mul_le_mul_of_nonneg_left h₂.le hc₂
    by_cases hpos : 0 < c₁
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h₁ hpos) hle₂
    · have hp : 0 < c₂ := by linarith
      exact add_lt_add_of_le_of_lt hle₁ (mul_lt_mul_of_pos_left h₂ hp)
  constructor
  · refine ⟨convex_univ, ?_⟩
    intro t ht r hr u v hu hv huv
    have h₁ := mul_le_mul_of_nonneg_left (hg₁.2 ht hr hu hv huv) hc₁
    have h₂ := mul_le_mul_of_nonneg_left (hg₂.2 ht hr hu hv huv) hc₂
    simp only [smul_eq_mul] at *
    nlinarith [h₁,h₂]
  · intro t ht
    change IsMinOn (fun t => c₁ * g₁ t + c₂ * g₂ t) Set.univ t at ht
    constructor
    · by_contra hn
      have hlt : t < min a₁ a₂ := lt_of_not_ge hn
      have h₁ := convex_left_decrease g₁ hg₁ a₁ b₁ hab₁ hmin₁ t
        (min a₁ a₂) hlt (min_le_left _ _)
      have h₂ := convex_left_decrease g₂ hg₂ a₂ b₂ hab₂ hmin₂ t
        (min a₁ a₂) hlt (min_le_right _ _)
      exact (not_lt_of_ge (isMinOn_iff.mp ht _ (Set.mem_univ _))) (hstrict h₁ h₂)
    · by_contra hn
      have hlt : max b₁ b₂ < t := lt_of_not_ge hn
      have h₁ := convex_right_increase g₁ hg₁ a₁ b₁ hab₁ hmin₁
        (max b₁ b₂) t (le_max_left _ _) hlt
      have h₂ := convex_right_increase g₂ hg₂ a₂ b₂ hab₂ hmin₂
        (max b₁ b₂) t (le_max_right _ _) hlt
      exact (not_lt_of_ge (isMinOn_iff.mp ht _ (Set.mem_univ _))) (hstrict h₁ h₂)

end MixtureCodex


end


section
set_option autoImplicit false
open MeasureTheory
theorem solution (g₁ g₂ : ℝ → ℝ)
    (hg₁ : ConvexOn ℝ Set.univ g₁) (hg₂ : ConvexOn ℝ Set.univ g₂)
    (a₁ b₁ a₂ b₂ : ℝ) (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hmin₁ : {t : ℝ | IsMinOn g₁ Set.univ t} = Set.Icc a₁ b₁)
    (hmin₂ : {t : ℝ | IsMinOn g₂ Set.univ t} = Set.Icc a₂ b₂)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ + c₂) :
    ConvexOn ℝ Set.univ (fun t => c₁ * g₁ t + c₂ * g₂ t) ∧
      {t : ℝ | IsMinOn (fun t => c₁ * g₁ t + c₂ * g₂ t) Set.univ t} ⊆
        Set.Icc (min a₁ a₂) (max b₁ b₂) := MixtureCodex.two_convex_argmin g₁ g₂ hg₁ hg₂ a₁ b₁ a₂ b₂ hab₁ hab₂ hmin₁ hmin₂ c₁ c₂ hc₁ hc₂ hc

end

#print axioms solution
