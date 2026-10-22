-- Prove2me | solution 1 for PetruzziDada.Additive.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:11:07.370611+00:00
-- url     : https://prove2.me/submissions/3ef4f857-1ec4-40fd-8500-72342fc4d8e2

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory
open PetruzziDada.Additive

namespace G69PD
variable (M : Model)

lemma f_eq_ind : M.f = (Set.Icc M.A M.B).indicator M.f := by
  funext u; by_cases hu : u ∈ Set.Icc M.A M.B
  · simp [hu]
  · simp [hu, M.f_eq_zero u hu]

lemma intOn : IntegrableOn M.f (Set.Icc M.A M.B) := by
  have h := M.f_integrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le M.A_lt_B.le] at h
  exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr h

lemma intf : Integrable M.f := by
  rw [f_eq_ind M]; exact (integrable_indicator_iff measurableSet_Icc).mpr (intOn M)

lemma intuf : Integrable (fun u => u * M.f u) := by
  have : (fun u => u * M.f u) = (Set.Icc M.A M.B).indicator (fun u => u * M.f u) := by
    funext u; by_cases hu : u ∈ Set.Icc M.A M.B
    · simp [hu]
    · simp [hu, M.f_eq_zero u hu]
  rw [this]
  refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
  exact (intOn M).continuousOn_mul continuousOn_id isCompact_Icc

lemma ii (a b : ℝ) : IntervalIntegrable M.f volume a b := (intf M).intervalIntegrable
lemma iiu (a b : ℝ) : IntervalIntegrable (fun u => u * M.f u) volume a b := (intuf M).intervalIntegrable

lemma Fsplit (z : ℝ) : (∫ u in z..M.B, M.f u) = 1 - M.F z := by
  have := intervalIntegral.integral_add_adjacent_intervals (ii M M.A z) (ii M z M.B)
  rw [M.f_total] at this; unfold Model.F; linarith

lemma musplit (z : ℝ) : (∫ u in z..M.B, u * M.f u) = M.μ - ∫ u in M.A..z, u * M.f u := by
  have := intervalIntegral.integral_add_adjacent_intervals (iiu M M.A z) (iiu M z M.B)
  unfold Model.μ; linarith

lemma Λ_eq (z : ℝ) : M.Λ z = z * M.F z - ∫ u in M.A..z, u * M.f u := by
  unfold Model.Λ Model.F
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub ((ii M _ _).const_mul z) (iiu M _ _), intervalIntegral.integral_const_mul]

lemma Θ_eq (z : ℝ) : M.Θ z = (M.μ - ∫ u in M.A..z, u * M.f u) - z * (1 - M.F z) := by
  unfold Model.Θ
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (iiu M _ _) ((ii M _ _).const_mul z), intervalIntegral.integral_const_mul,
    musplit, Fsplit]

lemma eq1 (z p : ℝ) : M.expProfit z p = M.Ψ p - M.L z p := by
  have e1 : (∫ u in M.A..z, (p * (M.y p + u) - M.h * (z - u)) * M.f u)
      = (p * M.y p - M.h * z) * M.F z + (p + M.h) * ∫ u in M.A..z, u * M.f u := by
    have : (fun u => (p * (M.y p + u) - M.h * (z - u)) * M.f u)
        = fun u => (p * M.y p - M.h * z) * M.f u + (p + M.h) * (u * M.f u) := by funext u; ring
    rw [this, intervalIntegral.integral_add ((ii M _ _).const_mul _) ((iiu M _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; rfl
  have e2 : (∫ u in z..M.B, (p * (M.y p + z) - M.s * (u - z)) * M.f u)
      = (p * (M.y p + z) + M.s * z) * (1 - M.F z) - M.s * (M.μ - ∫ u in M.A..z, u * M.f u) := by
    have : (fun u => (p * (M.y p + z) - M.s * (u - z)) * M.f u)
        = fun u => (p * (M.y p + z) + M.s * z) * M.f u - M.s * (u * M.f u) := by funext u; ring
    rw [this, intervalIntegral.integral_sub ((ii M _ _).const_mul _) ((iiu M _ _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, Fsplit, musplit]
  unfold Model.expProfit Model.Ψ Model.L
  rw [e1, e2, Λ_eq, Θ_eq]
  ring


lemma Fcont : Continuous M.F := by
  unfold Model.F; exact intervalIntegral.continuous_primitive (ii M) M.A

lemma F_A : M.F M.A = 0 := by unfold Model.F; simp
lemma F_B : M.F M.B = 1 := M.f_total

lemma Λ_diff (z w : ℝ) : M.Λ w - M.Λ z - (w - z) * M.F z = ∫ u in z..w, (w - u) * M.f u := by
  rw [Λ_eq, Λ_eq]
  have h1 := intervalIntegral.integral_add_adjacent_intervals (ii M M.A z) (ii M z w)
  have h2 := intervalIntegral.integral_add_adjacent_intervals (iiu M M.A z) (iiu M z w)
  have h3 : (∫ u in z..w, (w - u) * M.f u) = w * (∫ u in z..w, M.f u) - ∫ u in z..w, u * M.f u := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub ((ii M _ _).const_mul w) (iiu M _ _), intervalIntegral.integral_const_mul]
  unfold Model.F at *
  rw [h3, ← h1, ← h2]; ring

lemma bound_le (z w : ℝ) (hzw : z ≤ w) :
    |∫ u in z..w, (w - u) * M.f u| ≤ |w - z| * |M.F w - M.F z| := by
  have hF : M.F w - M.F z = ∫ u in z..w, M.f u := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (ii M M.A z) (ii M z w)
    unfold Model.F; linarith
  have hnn : 0 ≤ ∫ u in z..w, (w - u) * M.f u :=
    intervalIntegral.integral_nonneg hzw (fun u hu => mul_nonneg (by linarith [hu.2]) (M.f_nonneg u))
  have hle : (∫ u in z..w, (w - u) * M.f u) ≤ ∫ u in z..w, (w - z) * M.f u := by
    apply intervalIntegral.integral_mono_on hzw
    · exact ((iiu M z w).const_mul (-1)).add ((ii M z w).const_mul w) |>.congr (by
        intro u _; simp only [Pi.add_apply]; ring)
    · exact (ii M z w).const_mul _
    · intro u hu; exact mul_le_mul_of_nonneg_right (by linarith [hu.1]) (M.f_nonneg u)
  rw [intervalIntegral.integral_const_mul, ← hF] at hle
  have hFnn : 0 ≤ M.F w - M.F z := by
    rw [hF]; exact intervalIntegral.integral_nonneg hzw (fun u _ => M.f_nonneg u)
  rw [abs_of_nonneg hnn, abs_of_nonneg (by linarith), abs_of_nonneg hFnn]; exact hle

lemma bound (z w : ℝ) : |∫ u in z..w, (w - u) * M.f u| ≤ |w - z| * |M.F w - M.F z| := by
  rcases le_total z w with h | h
  · exact bound_le M z w h
  · -- ∫_z^w (w-u) f = -∫_w^z (w-u) f, and 0 ≤ ∫_w^z (u - w) f ≤ (z-w)(F z - F w)
    have hF : M.F z - M.F w = ∫ u in w..z, M.f u := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals (ii M M.A w) (ii M w z)
      unfold Model.F; linarith
    have e : (∫ u in z..w, (w - u) * M.f u) = ∫ u in w..z, (u - w) * M.f u := by
      rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]; congr 1; funext u; ring
    have hnn : 0 ≤ ∫ u in w..z, (u - w) * M.f u :=
      intervalIntegral.integral_nonneg h (fun u hu => mul_nonneg (by linarith [hu.1]) (M.f_nonneg u))
    have hle : (∫ u in w..z, (u - w) * M.f u) ≤ ∫ u in w..z, (z - w) * M.f u := by
      apply intervalIntegral.integral_mono_on h
      · exact ((iiu M w z).sub ((ii M w z).const_mul w)).congr (by intro u _; simp only [Pi.sub_apply]; ring)
      · exact (ii M w z).const_mul _
      · intro u hu; exact mul_le_mul_of_nonneg_right (by linarith [hu.2]) (M.f_nonneg u)
    rw [intervalIntegral.integral_const_mul, ← hF] at hle
    have hFnn : 0 ≤ M.F z - M.F w := by
      rw [hF]; exact intervalIntegral.integral_nonneg h (fun u _ => M.f_nonneg u)
    rw [e, abs_of_nonneg hnn, abs_sub_comm w z, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg hFnn]
    exact hle

lemma Λ_deriv (z : ℝ) : HasDerivAt M.Λ (M.F z) z := by
  rw [hasDerivAt_iff_isLittleO]
  have hc : Filter.Tendsto (fun w => |M.F w - M.F z|) (nhds z) (nhds 0) := by
    have := ((Fcont M).tendsto z).sub_const (M.F z)
    simpa using this.abs
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with w hw
  have e := Λ_diff M z w
  rw [smul_eq_mul, show M.Λ w - M.Λ z - (w - z) * M.F z = _ from e, Real.norm_eq_abs, Real.norm_eq_abs]
  calc _ ≤ |w - z| * |M.F w - M.F z| := bound M z w
    _ ≤ ε * |w - z| := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hw.le (abs_nonneg _)

lemma Θ_eq' (z : ℝ) : M.Θ z = M.μ - z + M.Λ z := by rw [Θ_eq, Λ_eq]; ring

lemma Θ_deriv (z : ℝ) : HasDerivAt M.Θ (-(1 - M.F z)) z := by
  have : M.Θ = fun w => M.μ - w + M.Λ w := funext (Θ_eq' M)
  rw [this]
  have := ((hasDerivAt_const z M.μ).sub (hasDerivAt_id z)).add (Λ_deriv M z)
  refine this.congr_deriv ?_; ring

lemma F_deriv (z : ℝ) (hz : ContinuousAt M.f z) : HasDerivAt M.F (M.f z) z := by
  unfold Model.F
  exact intervalIntegral.integral_hasDerivAt_right (ii M _ _)
    ((intf M).aestronglyMeasurable.stronglyMeasurableAtFilter) hz

lemma eq5 (z p : ℝ) :
    HasDerivAt (fun z' => M.expProfit z' p) (-(M.c + M.h) + (p + M.s + M.h) * (1 - M.F z)) z := by
  have e : (fun z' => M.expProfit z' p) = fun z' => M.Ψ p - ((M.c + M.h) * M.Λ z' + (p + M.s - M.c) * M.Θ z') := by
    funext z'; rw [eq1]; rfl
  rw [e]
  have := (hasDerivAt_const z (M.Ψ p)).sub (((Λ_deriv M z).const_mul (M.c + M.h)).add ((Θ_deriv M z).const_mul (p + M.s - M.c)))
  refine this.congr_deriv ?_; ring

lemma quad (z p : ℝ) : M.expProfit z p = M.expProfit z (M.price z) - M.b * (p - M.price z) ^ 2 := by
  have hb := M.b_pos.ne'
  rw [eq1, eq1]; unfold Model.Ψ Model.L Model.y Model.price Model.p0
  field_simp; ring

lemma lem1 (z : ℝ) : (∀ p : ℝ, M.expProfit z p ≤ M.expProfit z (M.price z)) ∧
      ∀ p : ℝ, M.expProfit z p = M.expProfit z (M.price z) → p = M.price z := by
  constructor
  · intro p; rw [quad M z p]; nlinarith [M.b_pos, sq_nonneg (p - M.price z)]
  · intro p hp; rw [quad M z p] at hp
    have : M.b * (p - M.price z) ^ 2 = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left M.b_pos.ne'
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

lemma price_deriv (z : ℝ) : HasDerivAt M.price ((1 - M.F z) / (2 * M.b)) z := by
  have : M.price = fun w => M.p0 - M.Θ w / (2 * M.b) := rfl
  rw [this]
  have := (hasDerivAt_const z M.p0).sub ((Θ_deriv M z).div_const (2 * M.b))
  refine this.congr_deriv ?_; ring

lemma red_eq : M.reducedProfit = fun z => (M.price z - M.c) * (M.a - M.b * M.price z + M.μ)
    - ((M.c + M.h) * M.Λ z + (M.price z + M.s - M.c) * M.Θ z) := by
  funext z; unfold Model.reducedProfit; rw [eq1]; rfl

lemma dR1 (z : ℝ) : HasDerivAt M.reducedProfit
        (-(M.c + M.h) + (M.p0 + M.s + M.h - M.Θ z / (2 * M.b)) * (1 - M.F z)) z := by
  rw [red_eq]
  have hP := price_deriv M z
  have := ((hP.sub_const M.c).mul (((hasDerivAt_const z M.a).sub (hP.const_mul M.b)).add_const M.μ)).sub
    (((Λ_deriv M z).const_mul (M.c + M.h)).add (((hP.add_const M.s).sub_const M.c).mul (Θ_deriv M z)))
  refine this.congr_deriv ?_
  have hb := M.b_pos.ne'
  simp only [Pi.sub_apply]; unfold Model.price Model.p0; field_simp; ring

lemma R_eq : M.R = fun z => -(M.c + M.h) + (M.p0 + M.s + M.h - M.Θ z / (2 * M.b)) * (1 - M.F z) := by
  funext z; exact (dR1 M z).deriv

end G69PD


open MeasureTheory
open PetruzziDada.Additive
/-- Eq. (5), p. 184: `∂E[Π(z, p)]/∂z = -(c + h) + (p + s + h)[1 - F(z)]`, at every `z`
and every price `p`. -/
theorem solution (M : Model) (z p : ℝ) :
    HasDerivAt (fun z' => M.expProfit z' p) (-(M.c + M.h) + (p + M.s + M.h) * (1 - M.F z)) z := by
  exact G69PD.eq5 M z p

