-- Prove2me | solution 1 for RybinAI2026.P01.artanh_three_div_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T08:54:38.519288+00:00
-- url     : https://prove2.me/submissions/848cb3af-8569-4411-8b3d-105623904dbe

-- Candidate v6 for artanh_three_div_bound (repair-of 7173: RAW bridges + membership-first EqOn + pow-ne-fact) — remote verification authoritative.
-- Mirror of l2c_arctan_ineq_DRAFT.lean for w in (0,1):
-- artanh w > 3w/(3-w^2), via StrictMonoOn from positive derivative.
-- d/dw [artanh w - 3w/(3-w^2)] = 4w^4/((1-w^2)(3-w^2)^2).
-- Verified exact over rationals; inequality holds numerically at 0.1/0.5/0.9.
-- artanh via Real.artanh_eq_half_log + HasDerivAt.log (names verified present
-- in pinned rev c5ea003; Real.artanh PRESENT_IN_PINNED_INDEX @0df444a).
-- interior_Ico is ROOT namespace (NOT Set.-prefixed). Remote verification
-- still required after integration into the full proof.

import Mathlib
set_option autoImplicit false

theorem solution (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) :
    3 * w / (3 - w ^ 2) < Real.artanh w := by
  set f : ℝ → ℝ := fun w => Real.artanh w - 3 * w / (3 - w ^ 2) with hf
  have hcontA : ContinuousOn Real.artanh (Set.Ico (0 : ℝ) 1) := by
    have e : Set.EqOn Real.artanh
        (fun x : ℝ => (1 / 2) * Real.log ((1 + x) / (1 - x))) (Set.Ico 0 1) := by
      intro x hx
      rw [Real.artanh_eq_half_log ⟨by linarith [hx.1], hx.2.le⟩]
    have h2 : ContinuousOn (fun x : ℝ => (1 / 2) * Real.log ((1 + x) / (1 - x)))
        (Set.Ico (0 : ℝ) 1) := by
      apply ContinuousOn.mul continuous_const.continuousOn
      have hinner : ContinuousOn (fun x : ℝ => (1 + x) / (1 - x)) (Set.Ico (0 : ℝ) 1) := by
        apply ContinuousOn.div
        · exact (continuous_const.add continuous_id).continuousOn
        · exact (continuous_const.sub continuous_id).continuousOn
        · intro x hx
          exact ne_of_gt (by linarith [hx.2])
      have hmaps : Set.MapsTo (fun x : ℝ => (1 + x) / (1 - x)) (Set.Ico (0 : ℝ) 1) {0}ᶜ := by
        intro x hx
        have h1 : (0 : ℝ) < (1 + x) / (1 - x) := by
          apply div_pos _ _
          · linarith [hx.1]
          · linarith [hx.2]
        exact h1.ne'
      exact Real.continuousOn_log.comp hinner hmaps
    exact h2.congr (fun x hx => e hx)
  have hcont : ContinuousOn f (Set.Ico 0 1) := by
    apply ContinuousOn.sub hcontA
    apply ContinuousOn.div
    · exact (continuous_const.mul continuous_id).continuousOn
    · exact (continuous_const.sub (continuous_id.pow 2)).continuousOn
    · intro x hx
      have : x ^ 2 < 1 := by
        have h1 : x < 1 := hx.2
        have h0 : 0 ≤ x := hx.1
        nlinarith [sq_nonneg (1 - x), h0, h1]
      exact ne_of_gt (by linarith)
  have hderiv : ∀ x : ℝ, x ∈ interior (Set.Ico (0 : ℝ) 1) →
      0 < deriv f x := by
    intro x hx
    have hxmem : x ∈ Set.Ioo (0 : ℝ) 1 := by
      have := interior_Ico (a := (0 : ℝ)) (b := 1)
      simpa [this] using hx
    have hx0 : (0 : ℝ) < x := hxmem.1
    have hx1 : x < 1 := hxmem.2
    have ha : HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
      have h1p : HasDerivAt (fun u : ℝ => 1 + u) (0 + 1) x := by
        have ha1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
        have hb1 : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id' x
        exact ha1.add hb1
      have h1m : HasDerivAt (fun u : ℝ => 1 - u) (0 - 1) x := by
        have ha1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
        have hb1 : HasDerivAt (fun u : ℝ => u) 1 x := hasDerivAt_id' x
        exact ha1.sub hb1
      have h1x : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      have h1px : (1 : ℝ) + x ≠ 0 := ne_of_gt (by linarith)
      have hq := h1p.div h1m h1x
      have hq2 : HasDerivAt (fun u : ℝ => (1 + u) / (1 - u)) (2 / (1 - x) ^ 2) x := by
        have hbridge : ((0 + 1 : ℝ) * (1 - x) - (1 + x) * (0 - 1)) / (1 - x) ^ 2
            = 2 / (1 - x) ^ 2 := by
          ring
        rwa [hbridge] at hq
      have hne2 : (1 + x) / (1 - x) ≠ 0 :=
        ne_of_gt (by apply div_pos <;> linarith)
      have hl := hq2.log hne2
      have hval : (1 / 2) * ((1 / (1 + x) + 1 / (1 - x))) = 1 / (1 - x ^ 2) := by
        have h1x2sq : ((1 : ℝ) - x) ^ 2 ≠ 0 := pow_ne_zero 2 h1x
        have h1x2 : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt (by nlinarith [hx0, hx1, sq_nonneg x])
        field_simp
        ring
      have hlog : HasDerivAt (fun u : ℝ => (1 / 2) * Real.log ((1 + u) / (1 - u)))
          ((1 / 2) * ((1 / (1 + x) + 1 / (1 - x)))) x := by
        have hc := HasDerivAt.const_mul (1 / 2) hl
        have hval2 : (1 / 2 : ℝ) * ((2 / (1 - x) ^ 2) / ((1 + x) / (1 - x)))
            = 1 / (1 - x ^ 2) := by
          have h1x2sq : ((1 : ℝ) - x) ^ 2 ≠ 0 := pow_ne_zero 2 h1x
          have h1x2 : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt (by nlinarith [hx0, hx1, sq_nonneg x])
          field_simp
          ring
        have hbridge2 : (1 / 2 : ℝ) * ((2 / (1 - x) ^ 2) / ((1 + x) / (1 - x)))
            = (1 / 2) * (1 / (1 + x) + 1 / (1 - x)) := by
          rw [hval2]
          exact hval.symm
        rwa [hbridge2] at hc
      have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hx1.le⟩
      have eart : Real.artanh x = (1 / 2) * Real.log ((1 + x) / (1 - x)) :=
        Real.artanh_eq_half_log hxIcc
      have hxmem' : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hx1⟩
      have heq : (fun u : ℝ => (1 / 2) * Real.log ((1 + u) / (1 - u))) =ᶠ[nhds x]
          Real.artanh := by
        filter_upwards [Ioo_mem_nhds hxmem'.1 hxmem'.2] with u hu
        exact (Real.artanh_eq_half_log ⟨by linarith [hu.1], (hu.2).le⟩).symm
      have h2 : HasDerivAt (fun u : ℝ => (1 / 2) * Real.log ((1 + u) / (1 - u)))
          (1 / (1 - x ^ 2)) x := by
        convert hlog using 1
        exact hval.symm
      exact h2.congr_of_eventuallyEq heq.symm
    have hb : HasDerivAt (fun u : ℝ => 3 * u / (3 - u ^ 2))
        ((3 * (3 - x ^ 2) - 3 * x * (0 - 2 * x)) / (3 - x ^ 2) ^ 2) x := by
      have hnum : HasDerivAt (fun u : ℝ => 3 * u) 3 x := hasDerivAt_const_mul 3
      have hdnm : HasDerivAt (fun u : ℝ => 3 - u ^ 2) (0 - 2 * x) x := by
        have ha3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x := hasDerivAt_const x 3
        have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
          have h := hasDerivAt_pow 2 x
          simpa using h
        exact ha3.sub h2
      exact hnum.div hdnm (ne_of_gt (by nlinarith [sq_nonneg x]))
    have hfab : HasDerivAt f (1 / (1 - x ^ 2)
        - (3 * (3 - x ^ 2) - 3 * x * (0 - 2 * x)) / (3 - x ^ 2) ^ 2) x :=
      ha.sub hb
    have hval : 1 / (1 - x ^ 2)
        - (3 * (3 - x ^ 2) - 3 * x * (0 - 2 * x)) / (3 - x ^ 2) ^ 2
        = 4 * x ^ 4 / ((1 - x ^ 2) * (3 - x ^ 2) ^ 2) := by
      have h1 : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt (by nlinarith [hx0, hx1, sq_nonneg x])
      have h3 : (3 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg x])
      field_simp
      ring
    rw [hfab.deriv, hval]
    apply div_pos _ _
    · exact mul_pos (by norm_num) (pow_pos hx0 4)
    · exact mul_pos (by nlinarith [hx0, hx1, sq_nonneg x]) (pow_pos (by nlinarith [sq_nonneg x]) 2)
  have hmono : StrictMonoOn f (Set.Ico 0 1) :=
    strictMonoOn_of_deriv_pos (convex_Ico 0 1) hcont hderiv
  have h0 : f 0 = 0 := by simp [hf, Real.artanh_zero]
  have hlt := hmono (Set.mem_Ico.mpr ⟨le_rfl, zero_lt_one⟩) (Set.mem_Ico.mpr ⟨hw0.le, hw1⟩) hw0
  rw [h0] at hlt
  have : f w = Real.artanh w - 3 * w / (3 - w ^ 2) := rfl
  linarith
