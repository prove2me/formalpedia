-- Prove2me | solution 1 for RobustMeanCov.OnePoint.twoPointValue_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:14:40.893222+00:00
-- url     : https://prove2.me/submissions/136bb7cc-944e-4381-8d52-6a4eb345bd95

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_twoPointValue

namespace RobustMeanCov.OnePoint

theorem aux_tpv_trap (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (a b : ℝ) (hab : a < b) :
    u b - u a ≤ (b - a) * (deriv u a + deriv u b) / 2 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  set c := (deriv u b - deriv u a) / (b - a) with hc
  let F : ℝ → ℝ := fun x => u x - deriv u a * (x - a) - c * (x - a) ^ 2 / 2
  have hF : ∀ x, HasDerivAt F (deriv u x - deriv u a - c * (x - a)) x := by
    intro x
    have h1 := (hu x).hasDerivAt
    have h2 : HasDerivAt (fun x => x - a) 1 x := (hasDerivAt_id' x).sub_const a
    have h3 := ((h2.pow 2).const_mul c).div_const 2
    have h4 := (h2.const_mul (deriv u a))
    have h := (h1.sub h4).sub h3
    have e : deriv u x - deriv u a * 1 - c * ((2 : ℕ) * (x - a) ^ (2 - 1) * 1) / 2
        = deriv u x - deriv u a - c * (x - a) := by push_cast; ring
    rw [e] at h
    exact h
  have hmono : AntitoneOn F (Set.Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    · exact fun x _ => (hF x).continuousAt.continuousWithinAt
    · intro x _; exact (hF x).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨hax, hxb⟩ := hx
      have key := hconv.2 (Set.mem_univ a) (Set.mem_univ b)
        (div_nonneg (sub_nonneg.mpr hxb.le) hba.le) (div_nonneg (sub_nonneg.mpr hax.le) hba.le)
        (by field_simp; ring)
      simp only [smul_eq_mul] at key
      have e1 : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by field_simp; ring
      have e2 : (b - x) / (b - a) * deriv u a + (x - a) / (b - a) * deriv u b
          = deriv u a + c * (x - a) := by rw [hc]; field_simp; ring
      rw [e1, e2] at key
      linarith
  have hFab := hmono ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ hab.le
  simp only [F, sub_self] at hFab
  have e3 : c * (b - a) ^ 2 = (deriv u b - deriv u a) * (b - a) := by
    rw [hc]; field_simp
  nlinarith

theorem aux_tpv_main (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m s : ℝ) (hs : 0 < s) :
    AntitoneOn (twoPointValue u m s) (Set.Ioo 0 1) := by
  have key : ∀ p ∈ Set.Ioo (0:ℝ) 1, ∃ E, HasDerivAt (twoPointValue u m s) E p ∧ E ≤ 0 := by
    rintro p ⟨hp0, hp1⟩
    have hp1' : 0 < 1 - p := sub_pos.mpr hp1
    have hg1 : HasDerivAt (fun y : ℝ => (1 - y) / y) ((-1 * p - (1 - p) * 1) / p ^ 2) p :=
      ((hasDerivAt_id' p).const_sub 1).div (hasDerivAt_id' p) hp0.ne'
    have hg2 : HasDerivAt (fun y : ℝ => y / (1 - y)) ((1 * (1 - p) - p * (-1)) / (1 - p) ^ 2) p :=
      (hasDerivAt_id' p).div ((hasDerivAt_id' p).const_sub 1) hp1'.ne'
    have hne1 : (1 - p) / p ≠ 0 := (div_pos hp1' hp0).ne'
    have hne2 : p / (1 - p) ≠ 0 := (div_pos hp0 hp1').ne'
    have hs1 := ((hg1.sqrt hne1).mul_const s).const_add m
    have hs2 := ((hg2.sqrt hne2).mul_const s).const_sub m
    have hu1 := (hu (m + √((1 - p) / p) * s)).hasDerivAt.comp p hs1
    have hu2 := (hu (m - √(p / (1 - p)) * s)).hasDerivAt.comp p hs2
    have hF := ((hasDerivAt_id' p).mul hu1).add (((hasDerivAt_id' p).const_sub 1).mul hu2)
    refine ⟨_, hF, ?_⟩
    simp only [Function.comp_apply]
    set r := √((1 - p) / p) with hr
    set q := √(p / (1 - p)) with hq
    have hr0 : 0 < r := Real.sqrt_pos.mpr (div_pos hp1' hp0)
    have hq0 : 0 < q := Real.sqrt_pos.mpr (div_pos hp0 hp1')
    have hrr : r * r = (1 - p) / p := Real.mul_self_sqrt (div_pos hp1' hp0).le
    have hqq : q * q = p / (1 - p) := Real.mul_self_sqrt (div_pos hp0 hp1').le
    have hrq : r * q = 1 := by
      rw [hr, hq, ← Real.sqrt_mul (div_pos hp1' hp0).le]
      rw [show (1 - p) / p * (p / (1 - p)) = 1 by field_simp]
      simp
    have hpr : p * r * (r + q) = 1 := by
      have : p * (r * r) = 1 - p := by rw [hrr]; field_simp
      linear_combination this + p * hrq
    have hqp : (1 - p) * q * (r + q) = 1 := by
      have : (1 - p) * (q * q) = p := by rw [hqq]; field_simp
      linear_combination this + (1 - p) * hrq
    have h1 : p * ((-1 * p - (1 - p) * 1) / p ^ 2 / (2 * r) * s) = -((r + q) * s / 2) := by
      field_simp
      linear_combination hpr
    have h2 : (1 - p) * -((1 * (1 - p) - p * -1) / (1 - p) ^ 2 / (2 * q) * s)
        = -((r + q) * s / 2) := by
      field_simp
      linear_combination hqp
    have trap := aux_tpv_trap u hu hconv (m - q * s) (m + r * s) (by nlinarith)
    have hE : u (m + r * s) + p * (deriv u (m + r * s) * ((-1 * p - (1 - p) * 1) / p ^ 2 / (2 * r) * s)) +
        (-1 * u (m - q * s) +
          (1 - p) * (deriv u (m - q * s) * -((1 * (1 - p) - p * -1) / (1 - p) ^ 2 / (2 * q) * s)))
        = (u (m + r * s) - u (m - q * s)) - ((m + r * s) - (m - q * s)) *
            (deriv u (m - q * s) + deriv u (m + r * s)) / 2 := by
      linear_combination (deriv u (m + r * s)) * h1 + (deriv u (m - q * s)) * h2
    rw [one_mul, hE]
    linarith
  choose! E hE hEle using key
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1) (f' := E)
  · intro x hx; exact (hE x hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Ioo] at hx; exact (hE x hx).hasDerivWithinAt
  · intro x hx; rw [interior_Ioo] at hx; exact hEle x hx

end RobustMeanCov.OnePoint

open RobustMeanCov.OnePoint

theorem solution (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m s : ℝ) (hs : 0 < s) :
    AntitoneOn (twoPointValue u m s) (Set.Ioo 0 1) :=
  aux_tpv_main u hu hconv m s hs
