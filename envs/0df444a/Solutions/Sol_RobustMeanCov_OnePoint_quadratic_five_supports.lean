-- Prove2me | solution 1 for RobustMeanCov.OnePoint.quadratic_five_supports
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:11:45.473219+00:00
-- url     : https://prove2.me/submissions/7cade86f-1548-4524-aaa7-f5f49ed634f4

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic
open Filter Topology Set

private theorem convex_support {D : Set ℝ} {f : ℝ → ℝ} (hc : ConvexOn ℝ D f)
    (m y d : ℝ) (hm : m ∈ D) (hy : y ∈ D) (hd : HasDerivAt f d m) :
    f m+d*(y-m) ≤ f y := by
  rcases lt_trichotomy m y with h | h | h
  · have hh:=hc.le_slope_of_hasDerivAt hm hy h hd
    simp only [slope_def_field] at hh
    have hh2:=(le_div_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · subst y; simp
  · have hh:=hc.slope_le_of_hasDerivAt hy hm h hd
    simp only [slope_def_field] at hh
    have hh2:=(div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

private theorem quadratic_lower (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L : ℝ) (hL : ∀ x,L ≤ deriv (deriv u) x)
    (m y : ℝ) : L/2*(y-m)^2+deriv u m*(y-m)+u m ≤ u y := by
  let g := fun x => u x-L/2*(x-m)^2
  let g' := fun x => deriv u x-L*(x-m)
  have hd1 : ∀ x,HasDerivAt g (g' x) x := by
    intro x
    convert! (hu x).hasDerivAt.sub ((((hasDerivAt_id x).sub_const m).pow 2).const_mul (L/2)) using 1 <;>
      (try dsimp [g,g']) <;> ring
  have hd2 : ∀ x,HasDerivAt g' (deriv (deriv u) x-L) x := by
    intro x
    convert! (hu' x).hasDerivAt.sub (((hasDerivAt_id x).sub_const m).const_mul L) using 1 <;>
      (try dsimp [g']) <;> ring
  have hc : ConvexOn ℝ univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (continuous_iff_continuousAt.mpr (fun x => (hd1 x).continuousAt)).continuousOn
      (fun x _ => (hd1 x).hasDerivWithinAt) (fun x _ => (hd2 x).hasDerivWithinAt)
    intro x hx
    exact sub_nonneg.mpr (hL x)
  have hh:=convex_support hc m y (g' m) (mem_univ _) (mem_univ _) (hd1 m)
  dsimp [g,g'] at hh
  nlinarith

private theorem quadratic_upper (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L a : ℝ) (hL : ∀ x ≤ a,deriv (deriv u) x ≤ L)
    (y : ℝ) (hy : y ≤ a) : u y ≤ L/2*(y-a)^2+deriv u a*(y-a)+u a := by
  let g := fun x => L/2*(x-a)^2-u x
  let g' := fun x => L*(x-a)-deriv u x
  have hd1 : ∀ x,HasDerivAt g (g' x) x := by
    intro x
    convert! ((((hasDerivAt_id x).sub_const a).pow 2).const_mul (L/2)).sub (hu x).hasDerivAt using 1 <;>
      (try dsimp [g,g']) <;> ring
  have hd2 : ∀ x,HasDerivAt g' (L-deriv (deriv u) x) x := by
    intro x
    convert! (((hasDerivAt_id x).sub_const a).const_mul L).sub (hu' x).hasDerivAt using 1 <;>
      (try dsimp [g']) <;> ring
  have hc : ConvexOn ℝ (Iic a) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Iic a)
      (continuous_iff_continuousAt.mpr (fun x => (hd1 x).continuousAt)).continuousOn
      (fun x _ => (hd1 x).hasDerivWithinAt) (fun x _ => (hd2 x).hasDerivWithinAt)
    intro x hx
    exact sub_nonneg.mpr (hL x (show x ∈ Iic a from interior_subset hx))
  have hh:=convex_support hc a y (g' a) (mem_Iic.mpr le_rfl) hy (hd1 a)
  dsimp [g,g'] at hh
  nlinarith

private theorem quadratic_ratio (A B C a m : ℝ) :
    Tendsto (fun y => (A*(y-a)^2+B*(y-a)+C)/(y-m)^2) atBot (𝓝 A) := by
  have hi : Tendsto (fun y : ℝ => (y-m)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atBot_zero.comp (by
      simpa only [sub_eq_add_neg,id_eq] using tendsto_atBot_add_const_right atBot (-m) tendsto_id)
  have hr : Tendsto (fun y : ℝ => (y-a)/(y-m)) atBot (𝓝 1) := by
    have hh:=(tendsto_const_nhds (x:=(1:ℝ))).add (hi.const_mul (m-a))
    simp only [mul_zero,add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_lt_atBot m] with y hy
    field_simp [sub_ne_zero.mpr (ne_of_lt hy)]
    ring
  have hh:=((hr.pow 2).const_mul A).add (((hr.mul hi).const_mul B).add ((hi.pow 2).const_mul C))
  simp only [one_pow,mul_one,mul_zero,zero_pow (by decide : 2≠0),add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_lt_atBot m] with y hy
  field_simp
  ring

private theorem ratio_upper_eventually (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (L m c : ℝ)
    (hL : ∀ᶠ x in atBot,deriv (deriv u) x ≤ L) (hc : L/2 < c) :
    ∀ᶠ y in atBot, u y/(y-m)^2 < c := by
  obtain ⟨a,ha⟩:=eventually_atBot.mp hL
  have hq:=quadratic_ratio (L/2) (deriv u a) (u a) a m
  have he:=(tendsto_order.mp hq).2 c hc
  filter_upwards [he,eventually_le_atBot a,eventually_lt_atBot m] with y hy hya hym
  have hbound:=quadratic_upper u hu hu' L a ha y hya
  have hdiv:=div_le_div_of_nonneg_right hbound (sq_nonneg (y-m))
  exact hdiv.trans_lt hy

private theorem derivative_lower (u : ℝ → ℝ) (hu' : Differentiable ℝ (deriv u))
    (hconv : ConvexOn ℝ univ (deriv u)) (L : ℝ)
    (hL : Tendsto (deriv (deriv u)) atBot (𝓝 L)) : ∀ x,L ≤ deriv (deriv u) x := by
  have hm:=hconv.monotoneOn_deriv (fun x _ => hu' x)
  intro x
  apply le_of_tendsto hL
  filter_upwards [eventually_le_atBot x] with y hy
  exact hm (mem_univ _) (mem_univ _) hy

private theorem ratio_finite (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (hconv : ConvexOn ℝ univ (deriv u))
    (L m : ℝ) (hL : Tendsto (deriv (deriv u)) atBot (𝓝 L)) :
    Tendsto (fun y => u y/(y-m)^2) atBot (𝓝 (L/2)) := by
  have hlo:=derivative_lower u hu' hconv L hL
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hq:=quadratic_ratio (L/2) (deriv u m) (u m) m m
    have he:=(tendsto_order.mp hq).1 c hc
    filter_upwards [he] with y hy
    exact hy.trans_le (div_le_div_of_nonneg_right (quadratic_lower u hu hu' L hlo m y) (sq_nonneg (y-m)))
  · intro c hc
    let K := L+(c-L/2)
    have hLK : L < K := by dsimp [K]; linarith
    have hKc : K/2 < c := by dsimp [K]; linarith
    exact ratio_upper_eventually u hu hu' K m c
      (((tendsto_order.mp hL).2 K hLK).mono fun _ h => h.le) hKc

private theorem ratio_infinite (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (m : ℝ)
    (hL : Tendsto (deriv (deriv u)) atBot atBot) :
    Tendsto (fun y => u y/(y-m)^2) atBot atBot := by
  apply tendsto_atBot.mpr
  intro c
  exact (ratio_upper_eventually u hu hu' (2*(c-1)) m c
    ((tendsto_atBot.mp hL) _) (by linarith)).mono fun _ h => h.le

theorem solution (u : ℝ → ℝ) (hconc : ConcaveOn ℝ Set.univ u)
    (hu : Differentiable ℝ u) (hu' : Differentiable ℝ (deriv u))
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (L : ℝ)
    (hL : Tendsto (deriv (deriv u)) atBot (𝓝 L)) (m : ℝ) :
    (∀ y : ℝ, 1 / 2 * L * (y - m) ^ 2 + deriv u m * (y - m) + u m ≤ u y) ∧
    IsGLB ((fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) '' {y | y ≠ m})
      (1 / 2 * L) ∧
    Tendsto (fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) atBot
      (𝓝 (1 / 2 * L)) := by
  have hlo:=derivative_lower u hu' hconv L hL
  have hq:=quadratic_lower u hu hu' L hlo m
  have hi : Tendsto (fun y : ℝ => (y-m)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atBot_zero.comp (by
      simpa only [sub_eq_add_neg,id_eq] using tendsto_atBot_add_const_right atBot (-m) tendsto_id)
  have hf : Tendsto (fun y : ℝ => (u y-u m)/(y-m)^2-deriv u m/(y-m)) atBot (𝓝 (1/2*L)) := by
    have hh:=((ratio_finite u hu hu' hconv L m hL).sub ((hi.pow 2).const_mul (u m))).sub
      (hi.const_mul (deriv u m))
    simp only [zero_pow (by decide : 2≠0),mul_zero,sub_zero] at hh
    convert hh using 1
    · ext y
      simp only [div_eq_mul_inv,inv_pow]
      ring
    · congr 1
      ring
  have hlower : ∀ y, y ≠ m → 1/2*L ≤ (u y-u m)/(y-m)^2-deriv u m/(y-m) := by
    intro y hym
    have hd : 0 < (y-m)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hym)
    have he : (u y-u m)/(y-m)^2-deriv u m/(y-m) =
        (u y-u m-deriv u m*(y-m))/(y-m)^2 := by field_simp <;> ring
    rw [he,le_div_iff₀ hd]
    nlinarith [hq y]
  refine ⟨?_,?_,hf⟩
  · intro y
    nlinarith [hq y]
  · constructor
    · rintro z ⟨y,hy,rfl⟩
      exact hlower y hy
    · intro b hb
      apply ge_of_tendsto hf
      filter_upwards [eventually_lt_atBot m] with y hy
      exact hb ⟨y,ne_of_lt hy,rfl⟩
