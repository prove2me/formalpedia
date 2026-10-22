-- Prove2me | solution 1 for PetruzziDada.Additive.theorem_1c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:40:34.08699+00:00
-- url     : https://prove2.me/submissions/cb535a92-6358-4e34-b08e-39d21e31b9cd

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


/-- derivative of R at continuity points of f, hazard-free form -/
lemma R_hasDeriv (w : ℝ) (hfc : ContinuousAt M.f w) : HasDerivAt M.R
    ((1 - M.F w) ^ 2 / (2 * M.b) - (M.p0 + M.s + M.h - M.Θ w / (2 * M.b)) * M.f w) w := by
  rw [R_eq]
  have hg : HasDerivAt (fun w => M.p0 + M.s + M.h - M.Θ w / (2 * M.b)) ((1 - M.F w) / (2 * M.b)) w :=
    ((hasDerivAt_const w (M.p0 + M.s + M.h)).sub ((Θ_deriv M w).div_const (2 * M.b))).congr_deriv (by ring)
  refine ((hasDerivAt_const w (-(M.c + M.h))).add (hg.mul ((hasDerivAt_const w (1:ℝ)).sub
    (F_deriv M w hfc)))).congr_deriv ?_
  simp only [Pi.sub_apply]; ring

lemma F_lt_one (z : ℝ) (hz : z < M.B) (hfc : ContinuousAt M.f z) (hfz : 0 < M.f z) : M.F z < 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hfc.eventually (lt_mem_nhds hfz))
  set c := min (z + ε / 2) M.B
  have hzc : z < c := lt_min (by linarith) hz
  have hpos : 0 < ∫ u in z..c, M.f u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (ii M _ _) _ hzc
    intro u hu
    apply hball
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2, min_le_left (z + ε / 2) M.B]
  have hnn : 0 ≤ ∫ u in c..M.B, M.f u :=
    intervalIntegral.integral_nonneg (min_le_right _ _) (fun u _ => M.f_nonneg u)
  have h1 := intervalIntegral.integral_add_adjacent_intervals (ii M z c) (ii M c M.B)
  have h2 := Fsplit M z
  linarith

lemma d2R (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B))
    (z : ℝ) (hz : z ∈ Set.Ioo M.A M.B) (hfz : 0 < M.f z) (hcrit : deriv M.R z = 0) :
    HasDerivAt (deriv M.R)
      (-(M.f z * (1 - M.F z) / (2 * M.b * M.hazard z ^ 2)) *
        (2 * M.hazard z ^ 2 + deriv M.hazard z)) z := by
  have hb := M.b_pos.ne'
  have hopen : Set.Ioo M.A M.B ∈ nhds z := Ioo_mem_nhds hz.1 hz.2
  have hcont : ∀ w ∈ Set.Ioo M.A M.B, ContinuousAt M.f w := fun w hw =>
    ((hf w hw).differentiableAt (Ioo_mem_nhds hw.1 hw.2)).continuousAt
  have hfd : HasDerivAt M.f (deriv M.f z) z := ((hf z hz).differentiableAt hopen).hasDerivAt
  set D := fun w => (1 - M.F w) ^ 2 / (2 * M.b) - (M.p0 + M.s + M.h - M.Θ w / (2 * M.b)) * M.f w
  have hev : deriv M.R =ᶠ[nhds z] D := by
    filter_upwards [hopen] with w hw
    exact (R_hasDeriv M w (hcont w hw)).deriv
  have hFd := F_deriv M z (hcont z hz)
  have hDz : D z = 0 := by rw [← hev.eq_of_nhds]; exact hcrit
  have ht : 1 - M.F z ≠ 0 := by have := F_lt_one M z hz.2 (hcont z hz) hfz; linarith
  have hf0 : M.f z ≠ 0 := hfz.ne'
  have hhaz : HasDerivAt M.hazard ((deriv M.f z * (1 - M.F z) - M.f z * (0 - M.f z)) / (1 - M.F z) ^ 2) z :=
    hfd.div ((hasDerivAt_const z (1:ℝ)).sub hFd) ht
  rw [hhaz.deriv]
  have hg : HasDerivAt (fun w => M.p0 + M.s + M.h - M.Θ w / (2 * M.b)) ((1 - M.F z) / (2 * M.b)) z :=
    ((hasDerivAt_const z (M.p0 + M.s + M.h)).sub ((Θ_deriv M z).div_const (2 * M.b))).congr_deriv (by ring)
  have hD : HasDerivAt D (2 * (1 - M.F z) * (0 - M.f z) / (2 * M.b)
      - ((1 - M.F z) / (2 * M.b) * M.f z + (M.p0 + M.s + M.h - M.Θ z / (2 * M.b)) * deriv M.f z)) z := by
    have := ((((hasDerivAt_const z (1:ℝ)).sub hFd).pow 2).div_const (2 * M.b)).sub (hg.mul hfd)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Pi.sub_apply]; ring
  refine (hD.congr_of_eventuallyEq hev).congr_deriv ?_
  set K := M.p0 + M.s + M.h - M.Θ z / (2 * M.b)
  have hK : K * M.f z - (1 - M.F z) ^ 2 / (2 * M.b) = 0 := by
    have : D z = (1 - M.F z) ^ 2 / (2 * M.b) - K * M.f z := rfl
    linarith
  have key : (2 * (1 - M.F z) * (0 - M.f z) / (2 * M.b) - ((1 - M.F z) / (2 * M.b) * M.f z + K * deriv M.f z))
      - (-(M.f z * (1 - M.F z) / (2 * M.b * M.hazard z ^ 2)) *
        (2 * M.hazard z ^ 2 + (deriv M.f z * (1 - M.F z) - M.f z * (0 - M.f z)) / (1 - M.F z) ^ 2))
      = -(deriv M.f z / M.f z) * (K * M.f z - (1 - M.F z) ^ 2 / (2 * M.b)) := by
    unfold Model.hazard; field_simp; ring
  rw [hK, mul_zero] at key; linarith

end G69PD

namespace G69PDC
open Set Filter

lemma pos_right {G : ℝ → ℝ} {G' w : ℝ} (h : HasDerivAt G G' w) (hG' : 0 < G') :
    ∃ δ > 0, ∀ t ∈ Ioo 0 δ, G w < G (w + t) := by
  have := h.tendsto_slope_zero_right.eventually (lt_mem_nhds hG')
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp this
  refine ⟨u, hu, fun t ht => ?_⟩
  have h1 : 0 < t⁻¹ • (G (w + t) - G w) := hsub ht
  rw [smul_eq_mul] at h1
  have := (pos_iff_pos_of_mul_pos h1).mp (inv_pos.mpr ht.1)
  linarith

lemma neg_left {G : ℝ → ℝ} {G' w : ℝ} (h : HasDerivAt G G' w) (hG' : 0 < G') :
    ∃ δ > 0, ∀ t ∈ Ioo 0 δ, G (w - t) < G w := by
  have := h.tendsto_slope_zero_left.eventually (lt_mem_nhds hG')
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp this
  refine ⟨-l, by simpa using hl, fun t ht => ?_⟩
  have h1 : 0 < (-t)⁻¹ • (G (w + -t) - G w) := hsub ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [smul_eq_mul] at h1
  have := (neg_iff_neg_of_mul_pos h1).mp (inv_lt_zero.mpr (by linarith [ht.1]))
  rw [← sub_eq_add_neg] at this
  linarith

lemma cross {G : ℝ → ℝ} {A B : ℝ} (hc : ContinuousOn G (Ioo A B))
    (hz : ∀ z ∈ Ioo A B, G z = 0 → ∃ G', 0 < G' ∧ HasDerivAt G G' z)
    {z1 z2 : ℝ} (h1 : z1 ∈ Ioo A B) (h2 : z2 ∈ Ioo A B) (h12 : z1 < z2) (hg : 0 ≤ G z1) :
    0 < G z2 := by
  by_contra hneg
  push Not at hneg
  -- a point z3 ∈ (z1, z2] with G z3 < 0
  obtain ⟨z3, hz13, hz32, hG3⟩ : ∃ z3, z1 < z3 ∧ z3 ≤ z2 ∧ G z3 < 0 := by
    rcases lt_or_eq_of_le hneg with h | h
    · exact ⟨z2, h12, le_rfl, h⟩
    · obtain ⟨G', hG', hd⟩ := hz z2 h2 h
      obtain ⟨δ, hδ, hδs⟩ := neg_left hd hG'
      obtain ⟨t, htd⟩ : ∃ t, t = min δ (z2 - z1) / 2 := ⟨_, rfl⟩
      have ht0 : 0 < t := by rw [htd]; have : 0 < z2 - z1 := by linarith
                             positivity
      have htδ : t < δ := by have := min_le_left δ (z2 - z1); linarith
      have ht2 : t < z2 - z1 := by have := min_le_right δ (z2 - z1); linarith
      refine ⟨z2 - t, by linarith, by linarith, ?_⟩
      have := hδs t ⟨ht0, htδ⟩; rw [h] at this; exact this
  have hsub : Icc z1 z3 ⊆ Ioo A B := fun x hx => ⟨lt_of_lt_of_le h1.1 hx.1, lt_of_le_of_lt (hx.2.trans hz32) h2.2⟩
  set K := Icc z1 z3 ∩ G ⁻¹' Ici 0
  have hK : IsClosed K := (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hKne : K.Nonempty := ⟨z1, ⟨le_rfl, hz13.le⟩, hg⟩
  have hKbdd : BddAbove K := ⟨z3, fun x hx => hx.1.2⟩
  set w := sSup K
  have hwK : w ∈ K := hK.csSup_mem hKne hKbdd
  have hwz3 : w < z3 := by
    rcases lt_or_eq_of_le hwK.1.2 with h | h
    · exact h
    · exfalso; have := hwK.2; rw [h] at this; exact absurd this (not_le.mpr hG3)
  have hright : ∀ z, w < z → z ≤ z3 → G z < 0 := by
    intro z hwz hz3
    by_contra hc'; push Not at hc'
    have : z ∈ K := ⟨⟨by linarith [hwK.1.1], hz3⟩, hc'⟩
    exact absurd (le_csSup hKbdd this) (not_le.mpr hwz)
  have hwI : w ∈ Ioo A B := hsub hwK.1
  -- find a point just right of w with G ≥ 0
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, ∀ t ∈ Ioo 0 δ, 0 ≤ G (w + t) := by
    rcases lt_or_eq_of_le (show (0:ℝ) ≤ G w from hwK.2) with hp | hp
    · have hca : ContinuousAt G w := hc.continuousAt (Ioo_mem_nhds hwI.1 hwI.2)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hca.eventually (lt_mem_nhds hp))
      refine ⟨ε, hε, fun t ht => (hball ?_).le⟩
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
    · obtain ⟨G', hG', hd⟩ := hz w hwI hp.symm
      obtain ⟨δ, hδ, hδs⟩ := pos_right hd hG'
      exact ⟨δ, hδ, fun t ht => by have := hδs t ht; rw [← hp] at this; exact this.le⟩
  obtain ⟨t, htd⟩ : ∃ t, t = min δ (z3 - w) / 2 := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htd]; have : 0 < z3 - w := by linarith
                         positivity
  have htδ : t < δ := by have := min_le_left δ (z3 - w); linarith
  have ht3 : t < z3 - w := by have := min_le_right δ (z3 - w); linarith
  have := hright (w + t) (by linarith) (by linarith)
  have := hδs t ⟨ht0, htδ⟩
  linarith

end G69PDC

namespace G69PD
open Set Filter
variable (M : Model)

lemma F_sub (z w : ℝ) : M.F w - M.F z = ∫ u in z..w, M.f u := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals (ii M M.A z) (ii M z w)
  unfold Model.F; linarith

lemma F_mono : Monotone M.F := fun z w h => by
  have := F_sub M z w
  have : 0 ≤ ∫ u in z..w, M.f u := intervalIntegral.integral_nonneg h (fun u _ => M.f_nonneg u)
  linarith

lemma F_le_one (w : ℝ) (hw : w ≤ M.B) : M.F w ≤ 1 := by
  have := Fsplit M w
  have : 0 ≤ ∫ u in w..M.B, M.f u := intervalIntegral.integral_nonneg hw (fun u _ => M.f_nonneg u)
  linarith

lemma F_lt_one_of_hz (hr : M.HazardCondition) (z : ℝ) (hz : z ∈ Ico M.A M.B) : M.F z < 1 := by
  by_contra hcon; push Not at hcon
  have hF1 : ∀ w ∈ Icc z M.B, M.F w = 1 := fun w hw =>
    le_antisymm (F_le_one M w hw.2) (hcon.trans (F_mono M hw.1))
  have hz0 : ∀ w ∈ Icc z M.B, M.hazard w = 0 := by
    intro w hw; unfold Model.hazard; rw [hF1 w hw]; simp
  obtain ⟨r', hd, hpos⟩ := hr z hz
  have hzI : z ∈ Icc z M.B := ⟨le_rfl, hz.2.le⟩
  have hd' : HasDerivWithinAt M.hazard r' (Icc z M.B) z := hd.mono (Icc_subset_Icc hz.1 le_rfl)
  have h0 : HasDerivWithinAt M.hazard 0 (Icc z M.B) z :=
    (hasDerivWithinAt_const z _ (0:ℝ)).congr (fun w hw => hz0 w hw) (hz0 z hzI)
  have := (uniqueDiffOn_Icc hz.2 z hzI).eq_deriv _ hd' h0
  rw [hz0 z hzI, this] at hpos; simp at hpos

lemma f_eq (hr : M.HazardCondition) (w : ℝ) (hw : w ∈ Ico M.A M.B) :
    M.f w = M.hazard w * (1 - M.F w) := by
  have := F_lt_one_of_hz M hr w hw
  unfold Model.hazard; field_simp [show (1 - M.F w) ≠ 0 by linarith]

lemma haz_deriv (hr : M.HazardCondition) (z : ℝ) (hz : z ∈ Ioo M.A M.B) :
    ∃ r', HasDerivAt M.hazard r' z ∧ 0 < 2 * M.hazard z ^ 2 + r' := by
  obtain ⟨r', hd, hpos⟩ := hr z ⟨hz.1.le, hz.2⟩
  exact ⟨r', hd.hasDerivAt (Icc_mem_nhds hz.1 hz.2), hpos⟩

lemma f_contAt (hr : M.HazardCondition) (z : ℝ) (hz : z ∈ Ioo M.A M.B) : ContinuousAt M.f z := by
  obtain ⟨r', hd, -⟩ := haz_deriv M hr z hz
  have hev : (fun w => M.hazard w * (1 - M.F w)) =ᶠ[nhds z] M.f := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact (f_eq M hr w ⟨hw.1.le, hw.2⟩).symm
  exact (hd.continuousAt.mul (continuous_const.sub (Fcont M)).continuousAt).congr hev

noncomputable def GG (z : ℝ) : ℝ :=
  2 * M.b * (M.p0 + M.s + M.h - M.Θ z / (2 * M.b)) * M.hazard z - (1 - M.F z)

lemma K_deriv (z : ℝ) :
    HasDerivAt (fun w => M.p0 + M.s + M.h - M.Θ w / (2 * M.b)) ((1 - M.F z) / (2 * M.b)) z :=
  ((hasDerivAt_const z (M.p0 + M.s + M.h)).sub ((Θ_deriv M z).div_const (2 * M.b))).congr_deriv (by ring)

lemma GG_deriv (hr : M.HazardCondition) (z : ℝ) (hz : z ∈ Ioo M.A M.B) (r' : ℝ)
    (hd : HasDerivAt M.hazard r' z) :
    HasDerivAt (GG M) (2 * M.b * ((1 - M.F z) / (2 * M.b)) * M.hazard z
      + 2 * M.b * (M.p0 + M.s + M.h - M.Θ z / (2 * M.b)) * r' - (0 - M.f z)) z := by
  have e : GG M = fun w => 2 * M.b * (M.p0 + M.s + M.h - M.Θ w / (2 * M.b)) * M.hazard w - (1 - M.F w) := rfl
  rw [e]
  exact (((K_deriv M z).const_mul (2 * M.b)).mul hd).sub
    ((hasDerivAt_const z (1:ℝ)).sub (F_deriv M z (f_contAt M hr z hz)))

lemma GG_zero (hr : M.HazardCondition) (z : ℝ) (hz : z ∈ Ioo M.A M.B) (h0 : GG M z = 0) :
    ∃ G', 0 < G' ∧ HasDerivAt (GG M) G' z := by
  obtain ⟨r', hd, hpos⟩ := haz_deriv M hr z hz
  refine ⟨_, ?_, GG_deriv M hr z hz r' hd⟩
  have hF := F_lt_one_of_hz M hr z ⟨hz.1.le, hz.2⟩
  have hfe := f_eq M hr z ⟨hz.1.le, hz.2⟩
  have hb := M.b_pos
  obtain ⟨K, hK⟩ : ∃ K, K = M.p0 + M.s + M.h - M.Θ z / (2 * M.b) := ⟨_, rfl⟩
  obtain ⟨r, hrr⟩ : ∃ r, r = M.hazard z := ⟨_, rfl⟩
  rw [← hK, ← hrr]
  rw [← hrr] at hfe hpos
  have hG : 2 * M.b * K * r = 1 - M.F z := by
    have : GG M z = 2 * M.b * K * r - (1 - M.F z) := by rw [hK, hrr]; rfl
    linarith
  have hr0 : 0 < r := by
    have hrnn : 0 ≤ r := by rw [hrr]; exact div_nonneg (M.f_nonneg z) (by linarith)
    rcases lt_or_eq_of_le hrnn with h | h
    · exact h
    · rw [← h] at hG; simp at hG; linarith
  have h2b : 2 * M.b * ((1 - M.F z) / (2 * M.b)) = 1 - M.F z := by field_simp
  have key : (2 * M.b * ((1 - M.F z) / (2 * M.b)) * r + 2 * M.b * K * r' - (0 - M.f z)) * r
      = (1 - M.F z) * (2 * r ^ 2 + r') := by
    linear_combination r ^ 2 * h2b + r' * hG + r * hfe
  have hprod : 0 < (2 * M.b * ((1 - M.F z) / (2 * M.b)) * r + 2 * M.b * K * r' - (0 - M.f z)) * r := by
    rw [key]; exact mul_pos (by linarith) hpos
  exact (pos_iff_pos_of_mul_pos hprod).mpr hr0

lemma Rderiv_eq (hr : M.HazardCondition) (z : ℝ) (hz : z ∈ Ioo M.A M.B) :
    deriv M.R z = -((1 - M.F z) / (2 * M.b)) * GG M z := by
  rw [(R_hasDeriv M z (f_contAt M hr z hz)).deriv, f_eq M hr z ⟨hz.1.le, hz.2⟩]
  have hb := M.b_pos.ne'
  unfold GG; field_simp; ring

lemma R_cont : Continuous M.R := by
  rw [R_eq]
  have hΘ : Continuous M.Θ := continuous_iff_continuousAt.2 fun z => (Θ_deriv M z).continuousAt
  have hF := Fcont M
  fun_prop

lemma GG_cont (hr : M.HazardCondition) : ContinuousOn (GG M) (Ioo M.A M.B) := fun z hz => by
  obtain ⟨r', hd, -⟩ := haz_deriv M hr z hz
  exact (GG_deriv M hr z hz r' hd).continuousAt.continuousWithinAt

lemma shape (hr : M.HazardCondition) : ∃ m ∈ Icc M.A M.B,
    (∀ z ∈ Ioo M.A m, 0 < deriv M.R z) ∧ (∀ z ∈ Ioo m M.B, deriv M.R z < 0) := by
  have hsgn : ∀ z ∈ Ioo M.A M.B, 0 < (1 - M.F z) / (2 * M.b) := fun z hz =>
    div_pos (by linarith [F_lt_one_of_hz M hr z ⟨hz.1.le, hz.2⟩]) (by linarith [M.b_pos])
  have hneg : ∀ z ∈ Ioo M.A M.B, GG M z < 0 → 0 < deriv M.R z := fun z hz hg => by
    rw [Rderiv_eq M hr z hz]; nlinarith [hsgn z hz]
  have hposd : ∀ z ∈ Ioo M.A M.B, 0 < GG M z → deriv M.R z < 0 := fun z hz hg => by
    rw [Rderiv_eq M hr z hz]; nlinarith [hsgn z hz]
  set S := {z ∈ Ioo M.A M.B | 0 ≤ GG M z}
  by_cases hS : S.Nonempty
  · have hbdd : BddBelow S := ⟨M.A, fun z hz => hz.1.1.le⟩
    obtain ⟨z0, hz0⟩ := hS
    have hmA : M.A ≤ sInf S := le_csInf ⟨z0, hz0⟩ (fun z hz => hz.1.1.le)
    have hmB : sInf S ≤ M.B := (csInf_le hbdd hz0).trans hz0.1.2.le
    refine ⟨sInf S, ⟨hmA, hmB⟩, ?_, ?_⟩
    · intro z hz
      have hzI : z ∈ Ioo M.A M.B := ⟨hz.1, lt_of_lt_of_le hz.2 hmB⟩
      apply hneg z hzI
      by_contra hc; push Not at hc
      exact absurd (csInf_le hbdd ⟨hzI, hc⟩) (not_le.mpr hz.2)
    · intro z hz
      have hzI : z ∈ Ioo M.A M.B := ⟨lt_of_le_of_lt hmA hz.1, hz.2⟩
      obtain ⟨s, hsS, hsz⟩ := exists_lt_of_csInf_lt ⟨z0, hz0⟩ hz.1
      exact hposd z hzI (G69PDC.cross (GG_cont M hr) (GG_zero M hr) hsS.1 hzI hsz hsS.2)
  · refine ⟨M.B, ⟨M.A_lt_B.le, le_rfl⟩, fun z hz => hneg z hz ?_, fun z hz => absurd hz.2 (by linarith [hz.1])⟩
    by_contra hc; push Not at hc
    exact hS ⟨z, hz, hc⟩

lemma unimodal (hr : M.HazardCondition) :
    (∃ m ∈ Icc M.A M.B, StrictMonoOn M.R (Icc M.A m) ∧ StrictAntiOn M.R (Icc m M.B)) ∧
      {z ∈ Icc M.A M.B | M.R z = 0}.encard ≤ 2 := by
  obtain ⟨m, hm, hinc, hdec⟩ := shape M hr
  have hmono : StrictMonoOn M.R (Icc M.A m) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) (R_cont M).continuousOn (by rw [interior_Icc]; exact hinc)
  have hanti : StrictAntiOn M.R (Icc m M.B) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) (R_cont M).continuousOn (by rw [interior_Icc]; exact hdec)
  refine ⟨⟨m, hm, hmono, hanti⟩, ?_⟩
  have hsub : {z ∈ Icc M.A M.B | M.R z = 0} ⊆
      {z ∈ Icc M.A m | M.R z = 0} ∪ {z ∈ Icc m M.B | M.R z = 0} := by
    rintro z ⟨hz, h0⟩
    rcases le_total z m with h | h
    · left; exact ⟨⟨hz.1, h⟩, h0⟩
    · right; exact ⟨⟨h, hz.2⟩, h0⟩
  have h1 : {z ∈ Icc M.A m | M.R z = 0}.encard ≤ 1 :=
    Set.encard_le_one_iff.2 fun a b ha hb => hmono.injOn ha.1 hb.1 (ha.2.trans hb.2.symm)
  have h2 : {z ∈ Icc m M.B | M.R z = 0}.encard ≤ 1 :=
    Set.encard_le_one_iff.2 fun a b ha hb => hanti.injOn ha.1 hb.1 (ha.2.trans hb.2.symm)
  calc _ ≤ _ := Set.encard_le_encard hsub
    _ ≤ _ := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

end G69PD


open MeasureTheory
open PetruzziDada.Additive
/-- Theorem 1(c), p. 185: if `2r(z)² + dr(z)/dz > 0` and `a - b(c - 2s) + A > 0`, then `z*`
is the unique `z ∈ [A, B]` with `dE[Π(z, p(z))]/dz = 0`, and stocking `q* = y(p*) + z*` at
`p* = p(z*)` is optimal for (4) over `z ∈ [A, B]` and every real price `p`. -/
theorem solution (M : Model) (hr : M.HazardCondition)
    (hpos : 0 < M.a - M.b * (M.c - 2 * M.s) + M.A) :
    ∃ zstar ∈ Set.Icc M.A M.B,
      {z ∈ Set.Icc M.A M.B | deriv M.reducedProfit z = 0} = {zstar} ∧
        ∀ z ∈ Set.Icc M.A M.B, ∀ p : ℝ, M.expProfit z p ≤ M.expProfit zstar (M.price zstar) := by
  obtain ⟨m, hm, hinc, hdec⟩ := G69PD.shape M hr
  have hRc := G69PD.R_cont M
  have hmono : StrictMonoOn M.R (Set.Icc M.A m) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hRc.continuousOn (by rw [interior_Icc]; exact hinc)
  have hanti : StrictAntiOn M.R (Set.Icc m M.B) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) hRc.continuousOn (by rw [interior_Icc]; exact hdec)
  have hb := M.b_pos
  have hRB : M.R M.B ≤ 0 := by
    rw [G69PD.R_eq]; simp only; rw [G69PD.F_B]; linarith [M.h_ge]
  have hRA : 0 < M.R M.A := by
    have hΘA : M.Θ M.A = M.μ - M.A := by rw [G69PD.Θ_eq, G69PD.F_A]; simp
    have e : 2 * M.b * M.R M.A = M.a - M.b * (M.c - 2 * M.s) + M.A := by
      rw [G69PD.R_eq]; simp only; rw [G69PD.F_A, hΘA]; unfold Model.p0; field_simp; ring
    have : 0 < 2 * M.b * M.R M.A := by rw [e]; exact hpos
    exact (pos_iff_pos_of_mul_pos this).mp (by linarith)
  have hRpos : ∀ z ∈ Set.Icc M.A m, 0 < M.R z := by
    intro z hz
    rcases eq_or_lt_of_le hz.1 with h | h
    · rw [← h]; exact hRA
    · exact lt_trans hRA (hmono ⟨le_rfl, hm.1⟩ hz h)
  have hRm : 0 < M.R m := hRpos m ⟨hm.1, le_rfl⟩
  obtain ⟨zs, hzs, hz0⟩ : ∃ zs ∈ Set.Icc m M.B, M.R zs = 0 :=
    intermediate_value_Icc' hm.2 hRc.continuousOn ⟨hRB, hRm.le⟩
  have hzsI : zs ∈ Set.Icc M.A M.B := ⟨hm.1.trans hzs.1, hzs.2⟩
  refine ⟨zs, hzsI, ?_, ?_⟩
  · ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, h0⟩
      change M.R z = 0 at h0
      rcases le_total z m with h | h
      · exact absurd h0 (hRpos z ⟨hz.1, h⟩).ne'
      · exact hanti.injOn ⟨h, hz.2⟩ hzs (h0.trans hz0.symm)
    · rintro rfl; exact ⟨hzsI, hz0⟩
  · have hdiff : ∀ z, HasDerivAt M.reducedProfit (M.R z) z := fun z =>
      (G69PD.dR1 M z).differentiableAt.hasDerivAt
    have hrc : Continuous M.reducedProfit :=
      continuous_iff_continuousAt.2 fun z => (hdiff z).continuousAt
    have hRge : ∀ z ∈ Set.Icc M.A zs, 0 ≤ M.R z := by
      intro z hz
      rcases le_total z m with h | h
      · exact (hRpos z ⟨hz.1, h⟩).le
      · rw [← hz0]; exact hanti.antitoneOn ⟨h, hz.2.trans hzs.2⟩ hzs hz.2
    have hRle : ∀ z ∈ Set.Icc zs M.B, M.R z ≤ 0 := by
      intro z hz
      rw [← hz0]; exact hanti.antitoneOn hzs ⟨hzs.1.trans hz.1, hz.2⟩ hz.1
    have hmon : MonotoneOn M.reducedProfit (Set.Icc M.A zs) :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _) hrc.continuousOn
        (fun z _ => (hdiff z).differentiableAt.differentiableWithinAt)
        (by rw [interior_Icc]; intro z hz; rw [(hdiff z).deriv]; exact hRge z ⟨hz.1.le, hz.2.le⟩)
    have hant : AntitoneOn M.reducedProfit (Set.Icc zs M.B) :=
      antitoneOn_of_deriv_nonpos (convex_Icc _ _) hrc.continuousOn
        (fun z _ => (hdiff z).differentiableAt.differentiableWithinAt)
        (by rw [interior_Icc]; intro z hz; rw [(hdiff z).deriv]; exact hRle z ⟨hz.1.le, hz.2.le⟩)
    intro z hz p
    have hle : M.reducedProfit z ≤ M.reducedProfit zs := by
      rcases le_total z zs with h | h
      · exact hmon ⟨hz.1, h⟩ ⟨hzsI.1, le_rfl⟩ h
      · exact hant ⟨le_rfl, hzs.2⟩ ⟨h, hz.2⟩ h
    calc M.expProfit z p ≤ M.expProfit z (M.price z) := (G69PD.lem1 M z).1 p
      _ = M.reducedProfit z := rfl
      _ ≤ M.reducedProfit zs := hle
      _ = _ := rfl

