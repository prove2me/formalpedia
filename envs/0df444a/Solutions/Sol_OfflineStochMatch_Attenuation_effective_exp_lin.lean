-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.effective_exp_lin
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:09:50.967031+00:00
-- url     : https://prove2.me/submissions/22bf3834-74b1-4759-bebe-d3e2932cded2

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting
set_option autoImplicit false

lemma oo_logconvex (g g1 g2 : ℝ → ℝ) (hg : ∀ z, HasDerivAt g (g1 z) z)
    (hg1 : ∀ z, HasDerivAt g1 (g2 z) z) (hpos : ∀ z ∈ Set.Icc (0:ℝ) 1, 0 < g z)
    (hineq : ∀ z ∈ Set.Ioo (0:ℝ) 1, g1 z ^ 2 ≤ g z * g2 z) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun z => Real.log (g z)) := by
  have hcont : ContinuousOn (fun z => Real.log (g z)) (Set.Icc 0 1) :=
    ContinuousOn.log (fun z _ => (hg z).continuousAt.continuousWithinAt) (fun z hz => (hpos z hz).ne')
  have hd1 : ∀ z ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun z => Real.log (g z)) (g1 z / g z) z := by
    intro z hz
    exact (hg z).log (hpos z ⟨hz.1.le, hz.2.le⟩).ne'
  have hd2 : ∀ z ∈ Set.Ioo (0:ℝ) 1,
      HasDerivAt (deriv fun z => Real.log (g z)) ((g2 z * g z - g1 z * g1 z) / (g z) ^ 2) z := by
    intro z hz
    have hne : g z ≠ 0 := (hpos z ⟨hz.1.le, hz.2.le⟩).ne'
    have h := (hg1 z).div (hg z) hne
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
    exact (hd1 w hw).deriv
  refine convexOn_of_deriv2_nonneg (convex_Icc 0 1) hcont ?_ ?_ ?_
  · rw [interior_Icc]; exact fun z hz => (hd1 z hz).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; exact fun z hz => (hd2 z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [interior_Icc] at hz
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [(hd2 z hz).deriv]
    have hp := hpos z ⟨hz.1.le, hz.2.le⟩
    apply div_nonneg _ (by positivity)
    nlinarith [hineq z hz]

lemma oo_exp_le (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : Real.exp (-(1/2 * z)) ≤ 1 - z / 4 := by
  have h1 : 0 < Real.exp (-(1/2 * z)) := Real.exp_pos _
  have h2 : (1 + z/2) ≤ Real.exp (z/2) := by linarith [Real.add_one_le_exp (z/2)]
  have h3 : Real.exp (-(1/2 * z)) * Real.exp (z/2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have h4 : Real.exp (-(1/2 * z)) * (1 + z/2) ≤ 1 := by
    calc _ ≤ Real.exp (-(1/2 * z)) * Real.exp (z/2) := mul_le_mul_of_nonneg_left h2 h1.le
      _ = 1 := h3
  have h5 : 1 ≤ (1 - z/4) * (1 + z/2) := by nlinarith
  have h6 : 0 < 1 + z/2 := by linarith
  by_contra hcon
  have hcon := not_le.1 hcon
  nlinarith [mul_lt_mul_of_pos_right hcon h6]

lemma oo_exp_eff : (∀ z ∈ Set.Icc (0 : ℝ) 1, Real.exp (-(1/2 * z)) ∈ Set.Icc (0 : ℝ) 1) ∧
    Real.exp (-(1/2 * 0)) = 1 ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun z => Real.log (1 - x * z * Real.exp (-(1/2 * z)))) := by
  refine ⟨?_, by simp, ?_⟩
  · intro z hz
    refine ⟨(Real.exp_pos _).le, ?_⟩
    exact Real.exp_le_one_iff.2 (by linarith [hz.1])
  · intro x hx
    have hE : ∀ z : ℝ, HasDerivAt (fun z => Real.exp (-(1/2 * z))) (Real.exp (-(1/2 * z)) * (-(1/2))) z := by
      intro z
      have := ((hasDerivAt_id z).const_mul (1/2 : ℝ)).neg.exp
      simpa using this
    refine oo_logconvex (fun z => 1 - x * z * Real.exp (-(1/2 * z)))
      (fun z => -x * Real.exp (-(1/2 * z)) * (1 - z/2))
      (fun z => x * Real.exp (-(1/2 * z)) * (1 - z/4)) ?_ ?_ ?_ ?_
    · intro z
      have h : HasDerivAt (fun z => 1 - x * z * Real.exp (-(1/2 * z)))
          (-(x * 1 * Real.exp (-(1/2 * z)) + x * z * (Real.exp (-(1/2 * z)) * (-(1/2))))) z :=
        (((hasDerivAt_id z).const_mul x).mul (hE z)).const_sub 1
      exact h.congr_deriv (by ring)
    · intro z
      have h1 : HasDerivAt (fun z : ℝ => -x * Real.exp (-(1/2 * z))) (-x * (Real.exp (-(1/2 * z)) * (-(1/2)))) z :=
        (hE z).const_mul (-x)
      have h2 : HasDerivAt (fun z : ℝ => 1 - z/2) (-(1/2)) z := by
        have := ((hasDerivAt_id z).div_const 2).const_sub 1
        simpa using this
      have h := h1.mul h2
      exact h.congr_deriv (by ring)
    · intro z hz
      have hE1 : Real.exp (-(1/2 * z)) ≤ 1 :=
        Real.exp_le_one_iff.2 (by linarith [hz.1])
      have hE0 := Real.exp_pos (-(1/2 * z))
      have h1 : z * Real.exp (-(1/2 * z)) ≤ 1 := by nlinarith [hz.1, hz.2]
      have : x * z * Real.exp (-(1/2 * z)) ≤ x := by nlinarith [hx.1, hx.2]
      linarith [hx.2]
    · intro z hz
      have hz0 := hz.1.le
      have hz1 := hz.2.le
      have hE0 := Real.exp_pos (-(1/2 * z))
      have hle := oo_exp_le z hz0 hz1
      have hx0 := hx.1
      have hx1 := hx.2
      have hxE : x * Real.exp (-(1/2 * z)) ≤ 1 - z/4 := by nlinarith
      have hxE0 : 0 < x * Real.exp (-(1/2 * z)) := mul_pos hx0 hE0
      set E := Real.exp (-(1/2 * z))
      -- (-x E (1-z/2))^2 ≤ (1 - x z E) * (x E (1 - z/4))
      have key : x * E ≤ 1 - z/4 := hxE
      have : (1 - x * z * E) * (x * E * (1 - z/4)) - (-x * E * (1 - z/2)) ^ 2
          = x * E * ((1 - z/4) - x * E) := by ring
      nlinarith [mul_nonneg hxE0.le (sub_nonneg.2 key)]


lemma oo_lin_eff : (∀ z ∈ Set.Icc (0 : ℝ) 1, (1 - 1/2 * z) ∈ Set.Icc (0 : ℝ) 1) ∧
    (1 - 1/2 * (0:ℝ)) = 1 ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun z => Real.log (1 - x * z * (1 - 1/2 * z))) := by
  refine ⟨?_, by norm_num, ?_⟩
  · intro z hz
    constructor <;> linarith [hz.1, hz.2]
  · intro x hx
    refine oo_logconvex (fun z => 1 - x * z * (1 - 1/2 * z))
      (fun z => -x * (1 - z)) (fun _ => x) ?_ ?_ ?_ ?_
    · intro z
      have h : HasDerivAt (fun z : ℝ => 1 - x * z * (1 - 1/2 * z))
          (-(x * 1 * (1 - 1/2 * z) + x * z * (-(1/2 * 1)))) z := by
        have h1 : HasDerivAt (fun z : ℝ => x * z) (x * 1) z := (hasDerivAt_id z).const_mul x
        have h2 : HasDerivAt (fun z : ℝ => 1 - 1/2 * z) (-(1/2 * 1)) z :=
          ((hasDerivAt_id z).const_mul (1/2 : ℝ)).const_sub 1
        exact (h1.mul h2).const_sub 1
      exact h.congr_deriv (by ring)
    · intro z
      have h : HasDerivAt (fun z : ℝ => -x * (1 - z)) (-x * -1) z :=
        ((hasDerivAt_id z).const_sub 1).const_mul (-x)
      exact h.congr_deriv (by ring)
    · intro z hz
      have : x * (z * (1 - 1/2 * z)) ≤ x * 1 := by
        apply mul_le_mul_of_nonneg_left _ hx.1.le
        nlinarith [hz.1, hz.2]
      show 0 < 1 - x * z * (1 - 1/2 * z)
      nlinarith [hx.2]
    · intro z hz
      have hz0 := hz.1.le
      have hz1 := hz.2.le
      have hx0 := hx.1
      have hx1 := hx.2
      have h1 : 1 - z + z^2/2 ≤ 1 := by nlinarith
      have h2 : 0 ≤ 1 - z + z^2/2 := by nlinarith
      have h3 : x * (1 - z + z^2/2) ≤ 1 := by nlinarith
      have : (1 - x * z * (1 - 1/2 * z)) * x - (-x * (1 - z)) ^ 2 = x * (1 - x * (1 - z + z^2/2)) := by ring
      show (-x * (1 - z)) ^ 2 ≤ (1 - x * z * (1 - 1/2 * z)) * x
      nlinarith [mul_nonneg hx0.le (sub_nonneg.2 h3)]

open OfflineStochMatch.Attenuation in
theorem solution : IsEffective (expAtt (1 / 2)) ∧ IsEffective (linAtt (1 / 2)) :=
  ⟨oo_exp_eff, oo_lin_eff⟩
