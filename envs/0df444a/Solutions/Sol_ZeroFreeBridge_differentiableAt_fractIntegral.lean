-- Prove2me | solution 1 for ZeroFreeBridge.differentiableAt_fractIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:52:49.576492+00:00
-- url     : https://prove2.me/submissions/7ffe2929-9d3e-489f-ad60-bda64579f789

import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Mathlib

/- (R2) DISCHARGE for `zeta_fract_repr_of`: the RHS integral

       fractIntegral s = ∫ x in Ioi 1, {x} · x^{-(s+1)} dx

   is complex-differentiable in `s` on the open right half-plane `{0 < Re s}`.
   This removes the `DifferentiableAt ℂ fractIntegral z` hypothesis (R2).

   Differentiation under the integral sign, via
   `hasDerivAt_integral_of_dominated_loc_of_lip`.  Parameter-derivative
   `F'(x) = {x} · (−log x) · x^{-(z+1)}`; on the neighbourhood `S = {z.re/2 < Re w}`
   the modulus of the w-derivative is dominated by `log x · x^{-(z.re/2 + 1)}`,
   integrable on `(1,∞)` because `z.re/2 > 0`.

   A gap-filler FEEDING input (R); NOT a proof of RH.  conjecture1_proved = False.
-/


open Set MeasureTheory Filter Topology

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ fractIntegral z := by
  have hσ : (0 : ℝ) < z.re / 2 := by linarith
  -- The parameter neighbourhood on which we dominate the derivative.
  set S : Set ℂ := {w : ℂ | z.re / 2 < w.re} with hSdef
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hSmem : S ∈ 𝓝 z := hSopen.mem_nhds (by rw [hSdef]; simp only [Set.mem_setOf_eq]; linarith)
  -- Integrand `F`, its w-derivative `F'`, and the dominating function `bound`.
  set F : ℂ → ℝ → ℂ := fun w x => fractIntegrand w x with hFdef
  set F' : ℝ → ℂ := fun x => ((Int.fract x : ℝ) : ℂ) * (-Complex.log x) / (x : ℂ) ^ (z + 1) with hF'def
  set bound : ℝ → ℝ := fun x => Real.log x * x ^ (-(z.re / 2) - 1) with hbdef
  -- (meas) `F w` is a.e.-strongly-measurable for every `w`, uniformly near `z`.
  have h_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hFdef, fractIntegrand]
    fun_prop
  -- (int) `F z` is integrable on `(1,∞)`: `‖F z x‖ ≤ x^{-(z.re+1)}` and `-(z.re+1) < -1`.
  have h_int : Integrable (F z) (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hbase : IntegrableOn (fun x : ℝ => ‖(x : ℂ) ^ (-(z + 1))‖) (Set.Ioi 1) := by
      have : (-(z + 1)).re < -1 := by simp [Complex.add_re]; linarith
      exact integrableOn_Ioi_norm_cpow_of_lt this (by norm_num)
    refine (Integrable.mono' hbase ?_ ?_)
    · refine (Measurable.aestronglyMeasurable ?_)
      simp only [hFdef, fractIntegrand]; fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : (1 : ℝ) < x := hx
      have hxpos : (0 : ℝ) < x := by linarith
      -- ‖{x}·x^{-(z+1)}‖ = {x}·‖x^{z+1}‖⁻¹ ≤ ‖x^{z+1}‖⁻¹ = ‖x^{-(z+1)}‖  (since 0 ≤ {x} ≤ 1)
      have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
      have hf1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
      have hpow : ‖(x : ℂ) ^ (-(z + 1))‖ = ‖(x : ℂ) ^ (z + 1)‖⁻¹ := by
        rw [Complex.cpow_neg, norm_inv]
      have hcnn : (0 : ℝ) ≤ ‖(x : ℂ) ^ (z + 1)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
      simp only [hFdef, fractIntegrand, norm_div, Complex.norm_real, Real.norm_of_nonneg hf0]
      rw [hpow, div_eq_mul_inv]
      calc Int.fract x * ‖(x : ℂ) ^ (z + 1)‖⁻¹
          ≤ 1 * ‖(x : ℂ) ^ (z + 1)‖⁻¹ := mul_le_mul_of_nonneg_right hf1 hcnn
        _ = ‖(x : ℂ) ^ (z + 1)‖⁻¹ := one_mul _
  -- (meas') `F'` is a.e.-strongly-measurable.
  have h_meas' : AEStronglyMeasurable F' (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine (Measurable.aestronglyMeasurable ?_)
    simp only [hF'def]; fun_prop
  -- (lip) Lipschitz-in-parameter, uniformly a.e.: from the derivative bound on the convex `S`.
  have h_lip : ∀ᵐ x ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      LipschitzOnWith (Real.nnabs (bound x)) (fun w => F w x) S := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    have hlogx : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (Complex.ofReal_log hxpos.le).symm
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hf0 : 0 ≤ Int.fract x := Int.fract_nonneg x
    have hf1 : Int.fract x ≤ 1 := (Int.fract_lt_one x).le
    -- the w-derivative of `fun w => F w x` at any point w (same shape as h_diff, general point)
    have hderiv : ∀ w : ℂ, HasDerivAt (fun v => F v x)
        (((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1))) w := by
      intro w
      have hlin : HasDerivAt (fun v : ℂ => -(v + 1)) (-1 : ℂ) w :=
        ((hasDerivAt_id w).add_const (1 : ℂ)).neg
      have hcpow : HasDerivAt (fun v : ℂ => (x : ℂ) ^ (-(v + 1)))
          ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1)) w :=
        hlin.const_cpow (Or.inl hxne)
      have hmul := hcpow.const_mul ((Int.fract x : ℝ) : ℂ)
      have hfun : (fun v => F v x) = (fun v : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(v + 1))) := by
        funext v; simp only [hFdef, fractIntegrand, div_eq_mul_inv, ← Complex.cpow_neg]
      rw [hfun]; exact hmul
    -- the derivative norm is ≤ bound x on S
    have hbd : ∀ w ∈ S, ‖((Int.fract x : ℝ) : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) * Complex.log (x : ℂ) * (-1))‖ ≤ bound x := by
      intro w hw
      rw [hSdef, Set.mem_setOf_eq] at hw
      have e1 : ‖((Int.fract x : ℝ) : ℂ)‖ = Int.fract x := by
        rw [Complex.norm_real, Real.norm_of_nonneg hf0]
      have e2 : ‖(x : ℂ) ^ (-(w + 1))‖ = x ^ (-(w.re + 1)) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]; congr 1
      have e3 : ‖Complex.log (x : ℂ)‖ = Real.log x := by
        rw [hlogx, Complex.norm_real, Real.norm_of_nonneg hlog0]
      rw [norm_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one, e1, e2, e3, hbdef]
      have hpow_le : x ^ (-(w.re + 1)) ≤ x ^ (-(z.re / 2) - 1) :=
        Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
      have hpow_pos : 0 < x ^ (-(w.re + 1)) := Real.rpow_pos_of_pos hxpos _
      -- after `norm_mul` the LHS associates as `{x} * (x^.. * log x)`
      have step1 : Int.fract x * (x ^ (-(w.re + 1)) * Real.log x)
          ≤ x ^ (-(w.re + 1)) * Real.log x :=
        mul_le_of_le_one_left (mul_nonneg hpow_pos.le hlog0) hf1
      have step2 : x ^ (-(w.re + 1)) * Real.log x ≤ Real.log x * x ^ (-(z.re / 2) - 1) := by
        rw [mul_comm (x ^ (-(w.re + 1)))]
        exact mul_le_mul_of_nonneg_left hpow_le hlog0
      exact le_trans step1 step2
    -- assemble via the convex derivative-bound Lipschitz lemma
    have hScvx : Convex ℝ S := by rw [hSdef]; exact convex_halfSpace_re_gt (z.re / 2)
    refine hScvx.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun w _ => (hderiv w).hasDerivWithinAt) (fun w hw => ?_)
    have hbnn : (0 : ℝ) ≤ bound x := by
      rw [hbdef]; exact mul_nonneg hlog0 (Real.rpow_pos_of_pos hxpos _).le
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg hbnn]
    exact hbd w hw
  -- (bint) the dominating function is integrable on `(1,∞)`: `log x · x^{-(z.re/2)-1}` is
  -- dominated by `(4/z.re)·x^{-(z.re/4)-1}` via `log x ≤ x^{z.re/4}/(z.re/4)`.
  have h_bint : Integrable bound (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hzne : z.re ≠ 0 := hz.ne'
    have hq : (-(z.re / 4) - 1) < -1 := by linarith
    have hg : Integrable (fun x : ℝ => (4 / z.re) * x ^ (-(z.re / 4) - 1))
        (volume.restrict (Set.Ioi 1)) :=
      (integrableOn_Ioi_rpow_of_lt hq one_pos).const_mul _
    refine Integrable.mono' hg ?_ ?_
    · simp only [hbdef]; fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : (1 : ℝ) < x := hx
      have hxpos : (0 : ℝ) < x := by linarith
      have hσ4 : (0 : ℝ) < z.re / 4 := by linarith
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      have hp1 : (0 : ℝ) < x ^ (-(z.re / 2) - 1) := Real.rpow_pos_of_pos hxpos _
      have hlogb : Real.log x ≤ x ^ (z.re / 4) / (z.re / 4) := by
        have h1 : Real.log (x ^ (z.re / 4)) ≤ x ^ (z.re / 4) - 1 :=
          Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos _)
        rw [Real.log_rpow hxpos] at h1
        rw [le_div_iff₀ hσ4]; nlinarith [h1]
      have hbnn : (0 : ℝ) ≤ bound x := by rw [hbdef]; exact mul_nonneg hlog0 hp1.le
      rw [Real.norm_of_nonneg hbnn, hbdef]
      calc Real.log x * x ^ (-(z.re / 2) - 1)
          ≤ (x ^ (z.re / 4) / (z.re / 4)) * x ^ (-(z.re / 2) - 1) := by gcongr
        _ = (4 / z.re) * x ^ (-(z.re / 4) - 1) := by
            rw [div_mul_eq_mul_div, ← Real.rpow_add hxpos,
              show z.re / 4 + (-(z.re / 2) - 1) = -(z.re / 4) - 1 by ring]
            field_simp
  -- (diff) the a.e. w-derivative of `F` at `z` is `F'`.
  have h_diff : ∀ᵐ x ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      HasDerivAt (fun w => F w x) (F' x) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    -- d/dw of `w ↦ (x)^{-(w+1)}` via `HasDerivAt.const_cpow` (chain rule, const base x);
    -- times the constant `{x}`.
    have hlin : HasDerivAt (fun w : ℂ => -(w + 1)) (-1 : ℂ) z :=
      ((hasDerivAt_id z).add_const (1 : ℂ)).neg
    have hcpow : HasDerivAt (fun w : ℂ => (x : ℂ) ^ (-(w + 1)))
        ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) z :=
      hlin.const_cpow (Or.inl hxne)
    have hmul := hcpow.const_mul ((Int.fract x : ℝ) : ℂ)
    -- massage the function into `F` and the derivative value into `F' x`.
    have hfun : (fun w => F w x) = (fun w : ℂ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(w + 1))) := by
      funext w; simp only [hFdef, fractIntegrand, div_eq_mul_inv, ← Complex.cpow_neg]
    have hval : ((Int.fract x : ℝ) : ℂ) * ((x : ℂ) ^ (-(z + 1)) * Complex.log (x : ℂ) * (-1)) = F' x := by
      simp only [hF'def, div_eq_mul_inv, ← Complex.cpow_neg]; ring
    rw [hfun, ← hval]
    exact hmul
  -- Assemble.
  have key := hasDerivAt_integral_of_dominated_loc_of_lip hSmem h_meas h_int h_meas' h_lip h_bint h_diff
  have hd : DifferentiableAt ℂ (fun w => ∫ x in Set.Ioi (1 : ℝ), F w x) z := key.2.differentiableAt
  have hfe : (fun w => ∫ x in Set.Ioi (1 : ℝ), F w x) = fractIntegral := by
    funext w; simp only [hFdef, fractIntegral]
  rwa [hfe] at hd
