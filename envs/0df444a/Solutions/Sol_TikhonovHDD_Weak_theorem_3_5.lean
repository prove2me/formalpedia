-- Prove2me | solution 1 for TikhonovHDD.Weak.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-23T07:41:30.349044+00:00
-- url     : https://prove2.me/submissions/ba836432-bea8-45fe-98ae-7deab616ccd9

import Mathlib
import Definitions.Def_TikhonovHDD_Weak_Setting

open Filter Topology Set MeasureTheory Asymptotics

open Filter Topology Set MeasureTheory

namespace TikhonovProof

noncomputable def gap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (x : ℝ → H) (z : H) (t : ℝ) : ℝ := g (x t) - g z

noncomputable def support {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → ℝ) (x : ℝ → H) (z : H) (t : ℝ) : ℝ :=
  inner ℝ (gradient g (x t)) (x t - z)

noncomputable def momentum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → ℝ) (x xd : ℝ → H) (β b : ℝ) (z : H) (t : ℝ) : H :=
  b • (x t - z) + t • (xd t + β • gradient g (x t))

noncomputable def energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (g : H → ℝ) (x xd : ℝ → H) (α β b : ℝ) (z : H) (t : ℝ) : ℝ :=
  (t^2 - β * (b + 2 - α) * t) * gap g x z t +
    ‖momentum g x xd β b z t‖^2 / 2 +
    b * (α - 1 - b) / 2 * ‖x t - z‖^2

end TikhonovProof

open Filter Topology Set MeasureTheory
open TikhonovHDD.Weak

namespace TikhonovProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem convex_gradient_support (g : H → ℝ) (hg : GenAssumptionG g) (a z : H) :
    g a - g z ≤ inner ℝ (gradient g a) (a - z) := by
  have hc : ConvexOn ℝ univ (fun s : ℝ => g (a + s • (z - a))) := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ u v hu hv huv
    have h := hg.1.2 (mem_univ (a + s • (z-a))) (mem_univ (a+t • (z-a))) hu hv huv
    have he : a + (u * s + v * t) • (z-a) =
        u • (a+s • (z-a)) + v • (a+t • (z-a)) := by
      calc
        _ = (u+v) • a + (u*s+v*t) • (z-a) := by rw [huv, one_smul]
        _ = _ := by module
    simpa only [smul_eq_mul, he] using h
  have hp : HasDerivAt (fun s : ℝ => a + s • (z-a)) (z-a) 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const (z-a)).const_add a
  have hd : HasDerivAt (fun s : ℝ => g (a+s • (z-a)))
      (fderiv ℝ g a (z-a)) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero] using
      (hg.2.1 a).hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have h := hc.le_slope_of_hasDerivWithinAt_Ioi (mem_univ 0) (mem_univ 1)
    (by norm_num : (0:ℝ)<1) hd.hasDerivWithinAt
  simp only [slope_def_field, zero_smul, add_zero, one_smul, add_sub_cancel,
    sub_zero, div_one] at h
  rw [← inner_gradient_left] at h
  have hi : inner ℝ (gradient g a) (z-a) = -inner ℝ (gradient g a) (a-z) := by
    rw [← inner_neg_right, neg_sub]
  linarith

omit [CompleteSpace H] in
theorem gap_nonneg (g : H → ℝ) (x : ℝ → H) (z : H) (hz : z ∈ argmin g) (t : ℝ) :
    0 ≤ gap g x z t := sub_nonneg.mpr (hz (x t))

theorem gap_le_support (g : H → ℝ) (hg : GenAssumptionG g) (x : ℝ → H) (z : H) (t : ℝ) :
    gap g x z t ≤ support g x z t := convex_gradient_support g hg (x t) z

theorem support_nonneg (g : H → ℝ) (hg : GenAssumptionG g) (x : ℝ → H)
    (z : H) (hz : z ∈ argmin g) (t : ℝ) : 0 ≤ support g x z t :=
  (gap_nonneg g x z hz t).trans (gap_le_support g hg x z t)

variable {g : H → ℝ} {ε : ℝ → ℝ} {α β t₀ : ℝ} {u₀ v₀ : H} {x xd xdd : ℝ → H}

theorem trajectory_deriv (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
    {t : ℝ} (ht : t₀ < t) : HasDerivAt x (xd t) t :=
  (hsol.1 t ht.le).hasDerivAt (mem_of_superset (Ioi_mem_nhds ht) Ioi_subset_Ici_self)

theorem velocity_deriv (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
    {t : ℝ} (ht : t₀ < t) : HasDerivAt xd (xdd t) t :=
  (hsol.2.1 t ht.le).hasDerivAt (mem_of_superset (Ioi_mem_nhds ht) Ioi_subset_Ici_self)

theorem trajectory_continuous (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) :
    ContinuousOn x (Ici t₀) := fun t ht => (hsol.1 t ht).continuousWithinAt

theorem velocity_continuous (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) :
    ContinuousOn xd (Ici t₀) := fun t ht => (hsol.2.1 t ht).continuousWithinAt

theorem gradient_deriv (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (fun s => gradient g (x s)) (fderiv ℝ (gradient g) (x t) (xd t)) t :=
  (hg.2.2.1 (x t)).hasFDerivAt.comp_hasDerivAt t (trajectory_deriv hsol ht)

theorem gap_deriv (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) (z : H) {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (gap g x z) (inner ℝ (gradient g (x t)) (xd t)) t := by
  have h := ((hg.2.1 (x t)).hasFDerivAt.comp_hasDerivAt t
    (trajectory_deriv hsol ht)).sub_const (g z)
  rw [← inner_gradient_left] at h
  exact h

theorem corrected_velocity_deriv (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (fun s => xd s + β • gradient g (x s))
      (-(α / t) • xd t - gradient g (x t) - ε t • x t) t := by
  have h := (velocity_deriv hsol ht).add ((gradient_deriv hg hsol ht).const_smul β)
  have he := hsol.2.2.2.1 t ht.le
  have heq : xdd t + β • fderiv ℝ (gradient g) (x t) (xd t) =
      -(α/t) • xd t - gradient g (x t) - ε t • x t := by
    apply eq_of_sub_eq_zero
    convert he using 1
    module
  rwa [heq] at h

theorem gap_continuous (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) (z : H) :
    ContinuousOn (gap g x z) (Ici t₀) :=
  (hg.2.1.continuous.comp_continuousOn (trajectory_continuous hsol)).sub continuousOn_const

theorem support_continuous (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) (z : H) :
    ContinuousOn (support g x z) (Ici t₀) :=
  (hg.2.2.1.continuous.comp_continuousOn (trajectory_continuous hsol)).inner
    ((trajectory_continuous hsol).sub continuousOn_const)

end TikhonovProof

open Filter Topology Set MeasureTheory

namespace TikhonovProof

theorem tail_intervalIntegrable (a : ℝ) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Ici a)) {t : ℝ} (ht : a ≤ t) :
    IntervalIntegrable F volume a t := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2
  exact (hF.mono fun _ hx => hx.1).integrableOn_Icc

theorem primitive_hasDerivAt (a : ℝ) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Ici a)) (t : ℝ) (ht : a < t) :
    HasDerivAt (fun u => ∫ s in a..u, F s) (F t) t := by
  apply intervalIntegral.integral_hasDerivAt_right (tail_intervalIntegrable a F hF ht.le)
  · exact (hF.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t ht
  · exact (hF t ht.le).continuousAt (Ici_mem_nhds ht)

theorem primitive_continuousOn (a : ℝ) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Ici a)) :
    ContinuousOn (fun t => ∫ s in a..t, F s) (Ici a) := by
  have hc : Continuous (fun t => F (max a t)) :=
    hF.comp_continuous (continuous_const.max continuous_id) (fun t => show a ≤ max a t from le_max_left a t)
  have hp := (intervalIntegral.continuous_primitive
    (fun s t => hc.intervalIntegrable (μ := volume) s t) a).continuousOn (s := Ici a)
  apply hp.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  change F s = F (max a s)
  rw [max_eq_right hs.1]

theorem primitive_tendsto (a : ℝ) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ici a)) :
    Tendsto (fun t => ∫ s in a..t, F s) atTop
      (𝓝 (∫ s in Ici a, F s)) := by
  rw [integral_Ici_eq_integral_Ioi]
  exact intervalIntegral_tendsto_integral_Ioi a (hF.mono_set Ioi_subset_Ici_self) tendsto_id

theorem primitive_norm_le (a : ℝ) (F : ℝ → ℝ)
    (hF : IntegrableOn F (Ici a)) {t : ℝ} (ht : a ≤ t) :
    ‖∫ s in a..t, F s‖ ≤ ∫ s in Ici a, ‖F s‖ := by
  calc
    ‖∫ s in a..t, F s‖ ≤ ∫ s in a..t, ‖F s‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ = ∫ s in Ioc a t, ‖F s‖ := intervalIntegral.integral_of_le ht
    _ ≤ ∫ s in Ici a, ‖F s‖ := by
      apply setIntegral_mono_set hF.norm
      · exact Filter.Eventually.of_forall fun s => norm_nonneg (F s)
      · exact Filter.Eventually.of_forall fun _ hs => hs.1.le

theorem derivative_le_integral (a : ℝ) (E E' F : ℝ → ℝ)
    (hE : ∀ t ∈ Ici a, HasDerivAt E (E' t) t)
    (hF : ContinuousOn F (Ici a))
    (hineq : ∀ t ∈ Ici a, E' t ≤ F t) {t : ℝ} (ht : a ≤ t) :
    E t ≤ E a + ∫ s in a..t, F s := by
  have hc : ContinuousOn E (Ici a) := fun s hs => (hE s hs).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun s => E s - ∫ v in a..s, F v) (Ici a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (hc.sub (primitive_continuousOn a F hF))
      (f' := fun s => E' s - F s)
    · intro s hs
      rw [interior_Ici] at hs
      change a < s at hs
      exact ((hE s hs.le).sub (primitive_hasDerivAt a F hF s hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      change a < s at hs
      exact sub_nonpos.mpr (hineq s hs.le)
  have hh := hm (show a ∈ Ici a from (show a ≤ a from le_rfl)) ht ht
  simpa only [intervalIntegral.integral_same, sub_zero, sub_le_iff_le_add, add_comm] using hh

theorem dissipation_integrable (a : ℝ) (E E' D F : ℝ → ℝ)
    (hE : ∀ t ∈ Ici a, HasDerivAt E (E' t) t)
    (hD : ContinuousOn D (Ici a)) (hFcont : ContinuousOn F (Ici a))
    (hF : IntegrableOn F (Ici a))
    (hEnonneg : ∀ t ∈ Ici a, 0 ≤ E t)
    (hDnonneg : ∀ t ∈ Ici a, 0 ≤ D t)
    (hineq : ∀ t ∈ Ici a, E' t + D t ≤ F t) :
    IntegrableOn D (Ici a) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (f := D) (b := a)).mpr
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (E a + ∫ s in Ici a, ‖F s‖) a
    (b := fun t : ℝ => t) (l := atTop)
  · intro t
    exact ((hD.mono (show Icc a t ⊆ Ici a from fun _ hs => hs.1)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  · exact tendsto_id
  · filter_upwards [eventually_ge_atTop a] with t ht
    have hi := derivative_le_integral a E E' (fun s => F s - D s)
      hE (hFcont.sub hD) (fun s hs => by linarith [hineq s hs]) ht
    rw [intervalIntegral.integral_sub (tail_intervalIntegrable a F hFcont ht)
      (tail_intervalIntegrable a D hD ht)] at hi
    have he := hEnonneg t ht
    have hf := (le_abs_self (∫ s in a..t, F s)).trans (primitive_norm_le a F hF ht)
    have hn : (∫ s in a..t, ‖D s‖) = ∫ s in a..t, D s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht] at hs
      exact Real.norm_of_nonneg (hDnonneg s hs.1)
    rw [hn]
    linarith

end TikhonovProof

open Filter Topology Set MeasureTheory

namespace TikhonovProof

theorem integrating_factor_bound (a : ℝ) (E E' q : ℝ → ℝ)
    (hE : ∀ t ∈ Ici a, HasDerivAt E (E' t) t)
    (hqcont : ContinuousOn q (Ici a)) (hq : IntegrableOn q (Ici a))
    (hEnonneg : ∀ t ∈ Ici a, 0 ≤ E t)
    (hqnonneg : ∀ t ∈ Ici a, 0 ≤ q t)
    (hineq : ∀ t ∈ Ici a, E' t ≤ q t * (E t + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ici a, E t ≤ C := by
  let P : ℝ → ℝ := fun t => ∫ s in a..t, q s
  let K : ℝ := ∫ s in Ici a, ‖q s‖
  have hEc : ContinuousOn E (Ici a) := fun t ht => (hE t ht).continuousAt.continuousWithinAt
  have hPc : ContinuousOn P (Ici a) := primitive_continuousOn a q hqcont
  have hm : AntitoneOn (fun t => Real.exp (-P t) * (E t + 1)) (Ici a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      ((Real.continuous_exp.comp_continuousOn hPc.neg).mul (hEc.add continuousOn_const))
      (f' := fun t => Real.exp (-P t) * (E' t - q t * (E t + 1)))
    · intro t ht
      rw [interior_Ici] at ht
      change a < t at ht
      have hd := ((primitive_hasDerivAt a q hqcont t ht).neg.exp).mul
        ((hE t ht.le).add_const 1)
      change HasDerivAt (fun s => Real.exp (-P s) * (E s + 1))
        (Real.exp (-P t) * (-q t) * (E t + 1) + Real.exp (-P t) * E' t) t at hd
      convert! hd.hasDerivWithinAt using 1
      ring
    · intro t ht
      rw [interior_Ici] at ht
      change a < t at ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hineq t ht.le))
  refine ⟨(E a + 1) * Real.exp K, mul_nonneg (by linarith [hEnonneg a (show a ≤ a from le_rfl)])
    (Real.exp_pos _).le, ?_⟩
  intro t ht
  have hm' := hm (show a ∈ Ici a from (show a ≤ a from le_rfl)) ht ht
  have hpa : P a = 0 := by simp [P]
  change Real.exp (-P t) * (E t + 1) ≤ Real.exp (-P a) * (E a + 1) at hm'
  rw [hpa, neg_zero, Real.exp_zero, one_mul] at hm'
  have he : E t + 1 ≤ (E a + 1) * Real.exp (P t) := by
    have hh := mul_le_mul_of_nonneg_left hm' (Real.exp_pos (P t)).le
    have hx : Real.exp (P t) * Real.exp (-P t) = 1 := by
      rw [← Real.exp_add]; simp
    calc
      E t + 1 = Real.exp (P t) * (Real.exp (-P t) * (E t + 1)) := by rw [← mul_assoc, hx, one_mul]
      _ ≤ Real.exp (P t) * (E a + 1) := hh
      _ = (E a + 1) * Real.exp (P t) := mul_comm _ _
  have hp : P t ≤ K := (le_abs_self _).trans (primitive_norm_le a q hq ht)
  have hb := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp)
    (show 0 ≤ E a + 1 by linarith [hEnonneg a (show a ≤ a from le_rfl)])
  have hq_used : 0 ≤ q a := hqnonneg a (show a ≤ a from le_rfl)
  linarith

theorem compensated_limit (a : ℝ) (E E' F : ℝ → ℝ)
    (hE : ∀ t ∈ Ici a, HasDerivAt E (E' t) t)
    (hFcont : ContinuousOn F (Ici a)) (hF : IntegrableOn F (Ici a))
    (hbelow : ∃ m : ℝ, ∀ t ∈ Ici a, m ≤ E t)
    (hineq : ∀ t ∈ Ici a, E' t ≤ F t) :
    ∃ l : ℝ, Tendsto E atTop (𝓝 l) := by
  let P : ℝ → ℝ := fun t => ∫ s in a..t, F s
  let H : ℝ → ℝ := fun t => E (max a t) - P (max a t)
  have hEc : ContinuousOn E (Ici a) := fun t ht => (hE t ht).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun t => E t - P t) (Ici a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (hEc.sub (primitive_continuousOn a F hFcont))
      (f' := fun t => E' t - F t)
    · intro t ht
      rw [interior_Ici] at ht
      change a < t at ht
      exact ((hE t ht.le).sub (primitive_hasDerivAt a F hFcont t ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change a < t at ht
      exact sub_nonpos.mpr (hineq t ht.le)
  have hH : Antitone H := fun s t hst =>
    hm (show a ≤ max a s from le_max_left a s) (show a ≤ max a t from le_max_left a t) (max_le_max_left a hst)
  obtain ⟨m, hm⟩ := hbelow
  have hB : BddBelow (range H) := by
    refine ⟨m - ∫ s in Ici a, ‖F s‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    have hp : P (max a t) ≤ ∫ s in Ici a, ‖F s‖ :=
      (le_abs_self _).trans (primitive_norm_le a F hF (le_max_left _ _))
    have he := hm (max a t) (show a ≤ max a t from le_max_left a t)
    change m - (∫ s in Ici a, ‖F s‖) ≤ E (max a t) - P (max a t)
    linarith
  have ht := (tendsto_atTop_ciInf hH hB).add (primitive_tendsto a F hF)
  refine ⟨(⨅ t, H t) + ∫ s in Ici a, F s, ht.congr' ?_⟩
  filter_upwards [eventually_ge_atTop a] with t ht
  simp [H, max_eq_right ht, P]

theorem euler_upper_bound (a c L : ℝ) (ha : 0 < a) (hc : 0 < c)
    (u u' : ℝ → ℝ) (hu : ∀ t ∈ Ici a, HasDerivAt u (u' t) t)
    (hupper : ∀ t ∈ Ici a, c * u t + t * u' t ≤ L) :
    ∃ C : ℝ, ∀ t ∈ Ici a, u t ≤ L / c + C * t ^ (-c) := by
  have hder : ∀ t ∈ Ici a, HasDerivAt (fun s => s ^ c * (u s - L / c))
      (t ^ (c - 1) * (c * u t + t * u' t - L)) t := by
    intro t ht
    have ht0 := ha.trans_le ht
    have hr : t ^ c = t ^ (c - 1) * t := by
      calc
        t ^ c = t ^ ((c - 1) + 1) := by congr 1; ring
        _ = t ^ (c - 1) * t := by rw [Real.rpow_add ht0, Real.rpow_one]
    convert! (Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).mul ((hu t ht).sub_const (L / c)) using 1
    rw [hr]
    field_simp [hc.ne']
    ring
  have hm : AntitoneOn (fun t => t ^ c * (u t - L / c)) (Ici a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (f' := fun t => t ^ (c - 1) * (c * u t + t * u' t - L))
    · intro t ht
      rw [interior_Ici] at ht
      change a < t at ht
      exact (hder t ht.le).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change a < t at ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (ha.le.trans ht.le) _)
        (sub_nonpos.mpr (hupper t ht.le))
  refine ⟨a ^ c * (u a - L / c), ?_⟩
  intro t ht
  have ht0 := ha.trans_le ht
  have hh := hm (show a ∈ Ici a from (show a ≤ a from le_rfl)) ht ht
  have hb : u t - L / c ≤ (a ^ c * (u a - L / c)) / t ^ c := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos ht0 c)).2
    simpa only [mul_comm] using hh
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
  linarith

theorem euler_limit (a c L : ℝ) (ha : 0 < a) (hc : 0 < c)
    (u u' : ℝ → ℝ) (hu : ∀ t ∈ Ici a, HasDerivAt u (u' t) t)
    (hlim : Tendsto (fun t => c * u t + t * u' t) atTop (𝓝 L)) :
    Tendsto u atTop (𝓝 (L / c)) := by
  apply Metric.tendsto_nhds.2
  intro η hη
  have he := (Metric.tendsto_nhds.1 hlim) (c * (η / 2)) (by positivity)
  obtain ⟨T, hT⟩ := (eventually_atTop.1 he)
  let A := max a T
  have hA : 0 < A := ha.trans_le (le_max_left _ _)
  have hupper : ∀ t ∈ Ici A, c * u t + t * u' t ≤ L + c * (η / 2) := by
    intro t ht
    have hh := hT t ((le_max_right _ _).trans ht)
    rw [Real.dist_eq] at hh
    have := (abs_lt.mp hh).2
    linarith
  have hlower : ∀ t ∈ Ici A, c * (-u t) + t * (-u' t) ≤ -L + c * (η / 2) := by
    intro t ht
    have hh := hT t ((le_max_right _ _).trans ht)
    rw [Real.dist_eq] at hh
    have := (abs_lt.mp hh).1
    linarith
  obtain ⟨C, hC⟩ := euler_upper_bound A c (L + c * (η / 2)) hA hc u u'
    (fun t ht => hu t (show a ≤ t from (le_max_left a T).trans ht)) hupper
  obtain ⟨D, hD⟩ := euler_upper_bound A c (-L + c * (η / 2)) hA hc
    (fun t => -u t) (fun t => -u' t)
    (fun t ht => (hu t (show a ≤ t from (le_max_left a T).trans ht)).neg) hlower
  have hCt : Tendsto (fun t : ℝ => C * t ^ (-c)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_rpow_neg_atTop hc))
  have hDt : Tendsto (fun t : ℝ => D * t ^ (-c)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_rpow_neg_atTop hc))
  filter_upwards [eventually_ge_atTop A, hCt.eventually (gt_mem_nhds (show 0 < η / 2 by positivity)),
    hDt.eventually (gt_mem_nhds (show 0 < η / 2 by positivity))] with t ht hct hdt
  have h1 := hC t ht
  have h2 := hD t ht
  have hplus : (L + c * (η / 2)) / c = L / c + η / 2 := by field_simp [hc.ne']
  have hminus : (-L + c * (η / 2)) / c = -(L / c) + η / 2 := by field_simp [hc.ne']
  rw [hplus] at h1
  rw [hminus] at h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end TikhonovProof

open Filter Topology Set MeasureTheory
open TikhonovHDD.Weak

namespace TikhonovProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {g : H → ℝ} {ε : ℝ → ℝ} {α β t₀ : ℝ} {u₀ v₀ : H} {x xd xdd : ℝ → H}

theorem momentum_deriv (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) (b : ℝ) (z : H)
    {t : ℝ} (ht : t₀ < t) (htpos : 0 < t) :
    HasDerivAt (momentum g x xd β b z)
      ((b+1-α) • xd t + (β-t) • gradient g (x t) - (t*ε t) • x t) t := by
  have h := ((trajectory_deriv hsol ht).sub_const z).const_smul b
  have hy := (hasDerivAt_id t).smul (corrected_velocity_deriv hg hsol ht)
  have heq : b • xd t + (1:ℝ) • (xd t + β • gradient g (x t)) +
      t • (-(α/t) • xd t - gradient g (x t) - ε t • x t) =
      (b+1-α) • xd t + (β-t) • gradient g (x t) - (t*ε t) • x t := by
    simp only [one_smul, smul_add, smul_sub, smul_smul, mul_neg, mul_div_cancel₀ α htpos.ne']
    module
  convert h.add hy using 1
  · rfl
  simpa only [id_eq, add_assoc, add_comm, add_left_comm] using heq.symm

theorem energy_hasDerivAt (hg : GenAssumptionG g)
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd) (b : ℝ) (z : H)
    {t : ℝ} (ht : t₀ < t) (htpos : 0 < t) :
    HasDerivAt (energy g x xd α β b z)
      ((2*t - β*(b+2-α)) * gap g x z t +
       (b+1-α)*t*‖xd t‖^2 + (β^2*t-β*t^2)*‖gradient g (x t)‖^2 -
       b*(t-β)*support g x z t - t*ε t*inner ℝ (x t) (momentum g x xd β b z t)) t := by
  have hp : HasDerivAt (fun s : ℝ => s^2 - β*(b+2-α)*s) (2*t-β*(b+2-α)) t := by
    convert ((hasDerivAt_id t).pow 2).sub ((hasDerivAt_id t).const_mul (β*(b+2-α))) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have he := ((hp.mul (gap_deriv hg hsol z ht)).add
    ((momentum_deriv hg hsol b z ht htpos).norm_sq.div_const 2)).add
    ((((trajectory_deriv hsol ht).sub_const z).norm_sq).const_mul (b*(α-1-b)/2))
  convert he using 1 <;> try rfl
  dsimp [momentum, support]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm (gradient g (x t)) (xd t),
    real_inner_comm (x t) (xd t),
    real_inner_comm (x t) (gradient g (x t)), real_inner_comm z (gradient g (x t)),
    real_inner_comm z (x t)]
  ring

theorem energy_difference (g : H → ℝ) (x xd : ℝ → H) (α β b₁ b₂ : ℝ) (z : H) (t : ℝ) :
    energy g x xd α β b₁ z t - energy g x xd α β b₂ z t =
      (b₁-b₂) * (-β*t*gap g x z t +
        t*inner ℝ (xd t + β • gradient g (x t)) (x t-z) + (α-1)/2*‖x t-z‖^2) := by
  simp only [energy, momentum, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (x t-z) (xd t+β • gradient g (x t))]
  ring

theorem energy_control (g : H → ℝ) (x xd : ℝ → H) (α β b : ℝ) (z : H)
    (hz : z ∈ argmin g) {t : ℝ} (hb : 0 < b) (hd : 0 < α-1-b)
    (hcoef : t^2 / 2 ≤ t^2-β*(b+2-α)*t) :
    0 ≤ energy g x xd α β b z t ∧
    t^2/2*gap g x z t ≤ energy g x xd α β b z t ∧
    ‖momentum g x xd β b z t‖^2/2 ≤ energy g x xd α β b z t ∧
    b*(α-1-b)/2*‖x t-z‖^2 ≤ energy g x xd α β b z t := by
  have hgap := gap_nonneg g x z hz t
  have hc : 0 ≤ t^2-β*(b+2-α)*t := (by positivity : 0 ≤ t^2/2).trans hcoef
  have hfirst := mul_nonneg hc hgap
  have hlast : 0 ≤ b*(α-1-b)/2*‖x t-z‖^2 := by positivity
  have hmid : 0 ≤ ‖momentum g x xd β b z t‖^2/2 := by positivity
  dsimp [energy]
  constructor
  · linarith only [hfirst, hlast, hmid]
  constructor
  · have h := mul_le_mul_of_nonneg_right hcoef hgap
    linarith only [h, hmid, hlast]
  constructor <;> linarith only [hfirst, hlast, hmid]

end TikhonovProof

open Filter Topology Set MeasureTheory
open TikhonovHDD.Weak
namespace TikhonovProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- A scalar tail with all coefficient signs explicit.
theorem late_coefficients (α β b t₀ : ℝ) (hβ : 0 ≤ β) (hb : 2 < b) :
    ∃ T : ℝ, t₀ < T ∧ 1 ≤ T ∧ ∀ t ∈ Ici T,
      t^2/2 ≤ t^2-β*(b+2-α)*t ∧ β ≤ t ∧
      2*t-β*(b+2-α)-b*(t-β) ≤ -(b-2)/2*t := by
  let T := max (max (t₀+1) 1)
    (max (2*|β*(b+2-α)|) (max β (2*|β*(α-2)|/(b-2))))
  refine ⟨T, ?_, ?_, ?_⟩
  · have := (le_max_left (t₀+1) 1).trans (le_max_left _ (max (2*|β*(b+2-α)|) (max β (2*|β*(α-2)|/(b-2)))))
    dsimp [T]; linarith
  · exact (le_max_right (t₀+1) 1).trans (le_max_left _ _)
  intro t ht
  have ht1 : 1 ≤ t := ((le_max_right (t₀+1) 1).trans (le_max_left _ _)).trans ht
  have htc : 2*|β*(b+2-α)| ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have htb : β ≤ t := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans ht
  have htd : 2*|β*(α-2)|/(b-2) ≤ t :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans ht
  have hd : 0 < b-2 := sub_pos.mpr hb
  have hd' := (div_le_iff₀ hd).mp htd
  have hc := le_abs_self (β*(b+2-α))
  have hc' := le_abs_self (β*(α-2))
  have ht0 : 0 ≤ t := by linarith only [ht1]
  have hp := mul_nonneg (by linarith only [htc,hc] : 0 ≤ t/2-β*(b+2-α)) ht0
  have _ := hβ
  refine ⟨?_, htb, ?_⟩
  · nlinarith only [hp]
  · nlinarith only [hd',hc']

noncomputable def energySlope (g : H → ℝ) (ε : ℝ → ℝ) (x xd : ℝ → H)
    (α β b : ℝ) (z : H) (t : ℝ) : ℝ :=
  (2*t-β*(b+2-α))*gap g x z t + (b+1-α)*t*‖xd t‖^2 +
    (β^2*t-β*t^2)*‖gradient g (x t)‖^2 - b*(t-β)*support g x z t -
    t*ε t*inner ℝ (x t) (momentum g x xd β b z t)

variable (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ)
  (u₀ v₀ : H) (x xd xdd : ℝ → H)
  (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : GenAssumptionG g)
  (hε : GenAssumptionEps t₀ ε ε')
  (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
  (hint : IntegrableOn (fun t => t * ε t) (Ici t₀)) (hα : 3 < α)

include ht₀ hβ hg hε hsol hint hα

theorem energy_tail_bound (z : H) (hz : z ∈ argmin g) (b : ℝ)
    (hb₀ : 2 < b) (hb₁ : b < α-1) :
    ∃ T C : ℝ, t₀ < T ∧ 1 ≤ T ∧ 0 ≤ C ∧ ∀ t ∈ Ici T,
      0 ≤ energy g x xd α β b z t ∧ energy g x xd α β b z t ≤ C ∧
      t^2/2*gap g x z t ≤ energy g x xd α β b z t ∧
      ‖momentum g x xd β b z t‖^2/2 ≤ energy g x xd α β b z t ∧
      b*(α-1-b)/2*‖x t-z‖^2 ≤ energy g x xd α β b z t := by
  obtain ⟨T,hT,hT1,hcoeff⟩ := late_coefficients α β b t₀ hβ hb₀
  let E := energy g x xd α β b z
  let d := b*(α-1-b)/2
  have hb : 0 < b := lt_trans (by norm_num) hb₀
  have hd : 0 < d := by dsimp [d]; positivity
  let C₀ := 1/d + ‖z‖^2 + 1
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let E' := fun t => (2*t-β*(b+2-α))*gap g x z t +
    (b+1-α)*t*‖xd t‖^2 + (β^2*t-β*t^2)*‖gradient g (x t)‖^2 -
    b*(t-β)*support g x z t - t*ε t*inner ℝ (x t) (momentum g x xd β b z t)
  have hc t (ht : t ∈ Ici T) := energy_control g x xd α β b z hz hb
    (sub_pos.mpr hb₁) (hcoeff t ht).1
  have hder t (ht : t ∈ Ici T) : HasDerivAt E (E' t) t :=
    energy_hasDerivAt hg hsol b z (hT.trans_le ht) (ht₀.trans (hT.trans_le ht))
  have hcont : ContinuousOn (fun t => C₀*(t*ε t)) (Ici T) :=
    continuousOn_const.mul (continuousOn_id.mul
      (ContinuousOn.mono (fun t ht => (hε.1 t ht).continuousWithinAt : ContinuousOn ε (Ici t₀))
        (Ici_subset_Ici.mpr hT.le)))
  have hi : IntegrableOn (fun t => C₀*(t*ε t)) (Ici T) :=
    (hint.mono_set (Ici_subset_Ici.mpr hT.le)).const_mul C₀
  have hineq t (ht : t ∈ Ici T) : E' t ≤ C₀*(t*ε t)*(E t+1) := by
    obtain ⟨hE,hgap,hW,hX⟩ := hc t ht
    have htpos : 0 ≤ t := (by linarith only [hT1] : 0 ≤ T).trans ht
    have heps := hε.2.2.1 t (hT.le.trans ht)
    have hJ := gap_le_support g hg x z t
    have hgap0 := gap_nonneg g x z hz t
    have hs : -b*(t-β)*support g x z t ≤ -b*(t-β)*gap g x z t :=
      mul_le_mul_of_nonpos_left hJ (by nlinarith only [(hcoeff t ht).2.1,hb])
    have hv : (b+1-α)*t*‖xd t‖^2 ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hb₁]) htpos
    have hgterm : (β^2*t-β*t^2)*‖gradient g (x t)‖^2 ≤ 0 := by
      have hh := mul_nonneg (mul_nonneg hβ htpos) (sub_nonneg.mpr (hcoeff t ht).2.1)
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hh]) (sq_nonneg _)
    have hgcoeff := mul_le_mul_of_nonneg_right (hcoeff t ht).2.2 hgap0
    have hneg : -(b-2)/2*t*gap g x z t ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hgap0
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hb₀]) htpos
    have hxdiv : ‖x t-z‖^2 ≤ E t/d := (le_div_iff₀ hd).mpr (by simpa [d,mul_comm] using hX)
    have hxnorm := norm_add_le (x t-z) z
    rw [sub_add_cancel] at hxnorm
    have hx2 : ‖x t‖^2 ≤ 2*‖x t-z‖^2+2*‖z‖^2 := by
      nlinarith only [hxnorm, norm_nonneg (x t), norm_nonneg (x t-z), norm_nonneg z,
        sq_nonneg (‖x t-z‖-‖z‖)]
    have hiabs := abs_real_inner_le_norm (x t) (momentum g x xd β b z t)
    have hi0 := neg_le_abs (inner ℝ (x t) (momentum g x xd β b z t))
    have hforcing : -inner ℝ (x t) (momentum g x xd β b z t) ≤ C₀*(E t+1) := by
      have hcross := sq_nonneg (‖x t‖-‖momentum g x xd β b z t‖)
      have hbound : ‖x t‖^2/2 + ‖momentum g x xd β b z t‖^2/2 ≤ E t/d+‖z‖^2+E t := by
        nlinarith only [hx2,hxdiv,hW]
      have hrest : E t/d+‖z‖^2+E t ≤ C₀*(E t+1) := by
        dsimp [C₀]
        have hp : 0 ≤ ‖z‖^2 * E t := mul_nonneg (sq_nonneg _) hE
        have hi := inv_nonneg.mpr hd.le
        simp only [div_eq_mul_inv, one_mul]
        nlinarith only [hi,hp]
      nlinarith only [hiabs,hi0,hcross,hbound,hrest]
    have hf := mul_le_mul_of_nonneg_left hforcing (mul_nonneg htpos heps)
    dsimp [E']
    nlinarith only [hs,hv,hgterm,hgcoeff,hneg,hf]
  obtain ⟨C,hC,hEC⟩ := integrating_factor_bound T E E' (fun t => C₀*(t*ε t))
    hder hcont hi (fun t ht => (hc t ht).1)
    (fun t ht => mul_nonneg hC₀ (mul_nonneg ((by linarith only [hT1] : 0 ≤ T).trans ht)
      (hε.2.2.1 t (hT.le.trans ht)))) hineq
  have _ := hα
  exact ⟨T,C,hT,hT1,hC,fun t ht => ⟨(hc t ht).1,hEC t ht,(hc t ht).2⟩⟩


theorem trajectory_bounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ t in atTop, ‖x t‖ ≤ R := by
  obtain ⟨z,hz⟩ := hg.2.2.2.2
  let b := (α+1)/2
  have hb₀ : 2 < b := by dsimp [b]; linarith only [hα]
  have hb₁ : b < α-1 := by dsimp [b]; linarith only [hα]
  obtain ⟨T,C,hT,hT1,hC,hbound⟩ := energy_tail_bound g ε ε' α β t₀ u₀ v₀ x xd xdd
    ht₀ hβ hg hε hsol hint hα z hz b hb₀ hb₁
  let d := b*(α-1-b)/2
  have hd : 0 < d := by
    have hb : 0 < b := by linarith only [hb₀]
    have hd' : 0 < α-1-b := sub_pos.mpr hb₁
    exact div_pos (mul_pos hb hd') (by norm_num)
  refine ⟨Real.sqrt (C/d)+‖z‖, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  have hx := (hbound t ht).2.2.2.2
  have hx2 : ‖x t-z‖^2 ≤ C/d := (le_div_iff₀ hd).mpr (by
    calc
      ‖x t-z‖^2*d = d*‖x t-z‖^2 := mul_comm _ _
      _ ≤ C := hx.trans (hbound t ht).2.1)
  have hxnorm : ‖x t-z‖ ≤ Real.sqrt (C/d) :=
    (Real.le_sqrt (norm_nonneg _) (div_nonneg hC hd.le)).mpr hx2
  have hh := norm_add_le (x t-z) z
  rw [sub_add_cancel] at hh
  linarith only [hxnorm,hh]

theorem scaled_gap_tendsto_zero (z : H) (hz : z ∈ argmin g) :
    Tendsto (fun t => t*gap g x z t) atTop (𝓝 0) := by
  let b := (α+1)/2
  have hb₀ : 2 < b := by dsimp [b]; linarith only [hα]
  have hb₁ : b < α-1 := by dsimp [b]; linarith only [hα]
  obtain ⟨T,C,hT,hT1,hC,hbound⟩ := energy_tail_bound g ε ε' α β t₀ u₀ v₀ x xd xdd
    ht₀ hβ hg hε hsol hint hα z hz b hb₀ hb₁
  apply squeeze_zero' (g := fun t : ℝ => 2*C/t)
  · filter_upwards [eventually_ge_atTop T] with t ht
    exact mul_nonneg (by linarith only [hT1,(show T ≤ t from ht)]) (gap_nonneg g x z hz t)
  · filter_upwards [eventually_ge_atTop T] with t ht
    have htpos : 0 < t := by linarith only [hT1,(show T ≤ t from ht)]
    apply (le_div_iff₀ htpos).mpr
    have h := (hbound t ht).2.2.1.trans (hbound t ht).2.1
    nlinarith only [h]
  · exact tendsto_const_nhds.div_atTop tendsto_id

theorem gap_tendsto_zero (z : H) (hz : z ∈ argmin g) :
    Tendsto (gap g x z) atTop (𝓝 0) := by
  have h := (scaled_gap_tendsto_zero g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz).div_atTop tendsto_id
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  exact mul_div_cancel_left₀ _ ht.ne'


theorem energy_dissipation_bound (z : H) (hz : z ∈ argmin g) (b : ℝ)
    (hb₀ : 2 < b) (hb₁ : b < α-1) :
    ∃ T K : ℝ, t₀ < T ∧ 1 ≤ T ∧ 0 ≤ K ∧ ∀ t ∈ Ici T,
      0 ≤ energy g x xd α β b z t ∧
      energySlope g ε x xd α β b z t + (b-2)/2*(t*gap g x z t) ≤ K*(t*ε t) ∧
      energySlope g ε x xd α β b z t + b/2*(t*support g x z t) ≤
        (2+|β*(b+2-α)|)*(t*gap g x z t)+K*(t*ε t) := by
  obtain ⟨T₁,C,hT₁,hT₁1,hC,hbound⟩ := energy_tail_bound g ε ε' α β t₀ u₀ v₀ x xd xdd
    ht₀ hβ hg hε hsol hint hα z hz b hb₀ hb₁
  obtain ⟨T₂,hT₂,hT₂1,hcoeff⟩ := late_coefficients α β b t₀ hβ hb₀
  let T := max T₁ (max T₂ (2*β))
  let d := b*(α-1-b)/2
  have hb : 0 < b := by linarith only [hb₀]
  have hd : 0 < d := by dsimp [d]; positivity
  let K := C/d + ‖z‖^2 + C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨T,K,hT₁.trans_le (le_max_left _ _),hT₁1.trans (le_max_left _ _),hK,?_⟩
  intro t ht
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ht
  have ht₂ : T₂ ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have htβ : 2*β ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
  have ht1 : 1 ≤ t := hT₁1.trans ht₁
  have ht0 : 0 ≤ t := by linarith only [ht1]
  have heps := hε.2.2.1 t (hT₁.le.trans ht₁)
  obtain ⟨hE,hEC,hgap,hW,hX⟩ := hbound t ht₁
  have hx2 : ‖x t-z‖^2 ≤ C/d := (le_div_iff₀ hd).mpr (by
    calc
      ‖x t-z‖^2*d = d*‖x t-z‖^2 := mul_comm _ _
      _ ≤ C := hX.trans hEC)
  have hxnorm := norm_add_le (x t-z) z
  rw [sub_add_cancel] at hxnorm
  have hxfull : ‖x t‖^2 ≤ 2*(C/d)+2*‖z‖^2 := by
    nlinarith only [hxnorm,hx2,norm_nonneg (x t),norm_nonneg (x t-z),norm_nonneg z,
      sq_nonneg (‖x t-z‖-‖z‖)]
  have hiabs := abs_real_inner_le_norm (x t) (momentum g x xd β b z t)
  have hineg := neg_le_abs (inner ℝ (x t) (momentum g x xd β b z t))
  have hinner : -inner ℝ (x t) (momentum g x xd β b z t) ≤ K := by
    dsimp [K]
    nlinarith only [hiabs,hineg,hxfull,hW,hEC,
      sq_nonneg (‖x t‖-‖momentum g x xd β b z t‖)]
  have hf := mul_le_mul_of_nonneg_left hinner (mul_nonneg ht0 heps)
  have hv : (b+1-α)*t*‖xd t‖^2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (by linarith only [hb₁]) ht0) (sq_nonneg _)
  have hgterm : (β^2*t-β*t^2)*‖gradient g (x t)‖^2 ≤ 0 := by
    have hh := mul_nonneg (mul_nonneg hβ ht0) (sub_nonneg.mpr (hcoeff t ht₂).2.1)
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hh]) (sq_nonneg _)
  have hgap0 := gap_nonneg g x z hz t
  have hJ := gap_le_support g hg x z t
  have hJ0 := support_nonneg g hg x z hz t
  have hs := mul_le_mul_of_nonpos_left hJ
    (by nlinarith only [hb,(hcoeff t ht₂).2.1] : -b*(t-β) ≤ 0)
  have hc := mul_le_mul_of_nonneg_right (hcoeff t ht₂).2.2 hgap0
  refine ⟨hE,?_,?_⟩
  · dsimp [energySlope]
    nlinarith only [hf,hv,hgterm,hs,hc]
  · have hsc : b/2*t ≤ b*(t-β) := by nlinarith only [hb,htβ]
    have hjc := mul_le_mul_of_nonneg_right hsc hJ0
    have hc' : 2*t-β*(b+2-α) ≤ (2+|β*(b+2-α)|)*t := by
      have hp := mul_nonneg (abs_nonneg (β*(b+2-α))) (by linarith only [ht1] : 0 ≤ t-1)
      have hn := neg_le_abs (β*(b+2-α))
      nlinarith only [hp,hn]
    have hc'g := mul_le_mul_of_nonneg_right hc' hgap0
    dsimp [energySlope]
    nlinarith only [hf,hv,hgterm,hjc,hc'g]


theorem energy_tendsto (z : H) (hz : z ∈ argmin g) (b : ℝ)
    (hb₀ : 2 < b) (hb₁ : b < α-1) :
    ∃ l : ℝ, Tendsto (energy g x xd α β b z) atTop (𝓝 l) := by
  obtain ⟨T,K,hT,hT1,hK,hbound⟩ := energy_dissipation_bound g ε ε' α β t₀ u₀ v₀ x xd xdd
    ht₀ hβ hg hε hsol hint hα z hz b hb₀ hb₁
  have hec : ContinuousOn ε (Ici T) :=
    ContinuousOn.mono (fun t ht => (hε.1 t ht).continuousWithinAt : ContinuousOn ε (Ici t₀))
      (Ici_subset_Ici.mpr hT.le)
  apply compensated_limit T (energy g x xd α β b z) (energySlope g ε x xd α β b z)
    (fun t => K*(t*ε t))
  · intro t ht
    exact energy_hasDerivAt hg hsol b z (hT.trans_le ht) (ht₀.trans (hT.trans_le ht))
  · exact continuousOn_const.mul (continuousOn_id.mul hec)
  · exact (hint.mono_set (Ici_subset_Ici.mpr hT.le)).const_mul K
  · exact ⟨0,fun t ht => (hbound t ht).1⟩
  · intro t ht
    have h := (hbound t ht).2.1
    have hn : 0 ≤ (b-2)/2*(t*gap g x z t) := mul_nonneg
      (by linarith only [hb₀]) (mul_nonneg (by linarith only [hT1,(show T ≤ t from ht)]) (gap_nonneg g x z hz t))
    linarith only [h,hn]

theorem support_integrable (z : H) (hz : z ∈ argmin g) :
    IntegrableOn (support g x z) (Ici (t₀+1)) := by
  let b := (α+1)/2
  have hb₀ : 2 < b := by dsimp [b]; linarith only [hα]
  have hb₁ : b < α-1 := by dsimp [b]; linarith only [hα]
  obtain ⟨T,K,hT,hT1,hK,hbound⟩ := energy_dissipation_bound g ε ε' α β t₀ u₀ v₀ x xd xdd
    ht₀ hβ hg hε hsol hint hα z hz b hb₀ hb₁
  have hec : ContinuousOn ε (Ici T) :=
    ContinuousOn.mono (fun t ht => (hε.1 t ht).continuousWithinAt : ContinuousOn ε (Ici t₀))
      (Ici_subset_Ici.mpr hT.le)
  have hgc := (gap_continuous hg hsol z).mono (Ici_subset_Ici.mpr hT.le)
  have hjc := (support_continuous hg hsol z).mono (Ici_subset_Ici.mpr hT.le)
  have hder t (ht : t ∈ Ici T) : HasDerivAt (energy g x xd α β b z)
      (energySlope g ε x xd α β b z t) t :=
    energy_hasDerivAt hg hsol b z (hT.trans_le ht) (ht₀.trans (hT.trans_le ht))
  have hFi : IntegrableOn (fun t => K*(t*ε t)) (Ici T) :=
    (hint.mono_set (Ici_subset_Ici.mpr hT.le)).const_mul K
  have hFc : ContinuousOn (fun t => K*(t*ε t)) (Ici T) :=
    continuousOn_const.mul (continuousOn_id.mul hec)
  have hgapI := dissipation_integrable T (energy g x xd α β b z)
    (energySlope g ε x xd α β b z) (fun t => (b-2)/2*(t*gap g x z t))
    (fun t => K*(t*ε t)) hder
    (continuousOn_const.mul (continuousOn_id.mul hgc)) hFc hFi
    (fun t ht => (hbound t ht).1)
    (fun t ht => mul_nonneg (by linarith only [hb₀])
      (mul_nonneg (by linarith only [hT1,(show T ≤ t from ht)]) (gap_nonneg g x z hz t)))
    (fun t ht => (hbound t ht).2.1)
  have hgapi : IntegrableOn (fun t => t*gap g x z t) (Ici T) := by
    have h := hgapI.const_mul (2/(b-2))
    have he : (fun t => 2/(b-2)*((b-2)/2*(t*gap g x z t))) =
        (fun t => t*gap g x z t) := by
      funext t
      field_simp [ne_of_gt (sub_pos.mpr hb₀)]
    rwa [he] at h
  have hsupI := dissipation_integrable T (energy g x xd α β b z)
    (energySlope g ε x xd α β b z) (fun t => b/2*(t*support g x z t))
    (fun t => (2+|β*(b+2-α)|)*(t*gap g x z t)+K*(t*ε t)) hder
    (continuousOn_const.mul (continuousOn_id.mul hjc))
    ((continuousOn_const.mul (continuousOn_id.mul hgc)).add hFc)
    ((hgapi.const_mul _).add hFi) (fun t ht => (hbound t ht).1)
    (fun t ht => mul_nonneg (by linarith only [hb₀])
      (mul_nonneg (by linarith only [hT1,(show T ≤ t from ht)]) (support_nonneg g hg x z hz t)))
    (fun t ht => (hbound t ht).2.2)
  have hsup : IntegrableOn (support g x z) (Ici T) := by
    apply hsupI.mono_nonneg (hjc.aestronglyMeasurable measurableSet_Ici)
    · exact (ae_restrict_mem measurableSet_Ici).mono fun t _ => support_nonneg g hg x z hz t
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have hn := support_nonneg g hg x z hz t
      have hcoef : 1 ≤ b/2*t := by nlinarith only [hb₀,hT1,(show T ≤ t from ht)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hcoef) hn]
  have hprefix : IntegrableOn (support g x z) (Icc (t₀+1) T) :=
    ((support_continuous hg hsol z).mono (fun t ht => by
      exact le_trans (by linarith) ht.1)).integrableOn_Icc
  exact (hprefix.union hsup).mono_set Ici_subset_Icc_union_Ici

end TikhonovProof

open Filter Topology Set MeasureTheory
open TikhonovHDD.Weak
namespace TikhonovProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ)
  (u₀ v₀ : H) (x xd xdd : ℝ → H)
  (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : GenAssumptionG g)
  (hε : GenAssumptionEps t₀ ε ε')
  (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
  (hint : IntegrableOn (fun t => t * ε t) (Ici t₀)) (hα : 3 < α)
include ht₀ hβ hg hε hsol hint hα

theorem distance_squared_limit (z : H) (hz : z ∈ argmin g) :
    ∃ l : ℝ, Tendsto (fun t => ‖x t-z‖^2) atTop (𝓝 l) := by
  let b₁ := 2+(α-3)/3
  let b₂ := 2+2*(α-3)/3
  have hb₁ : 2 < b₁ := by dsimp [b₁]; linarith only [hα]
  have hb₂ : 2 < b₂ := by dsimp [b₂]; linarith only [hα]
  have hb₁' : b₁ < α-1 := by dsimp [b₁]; linarith only [hα]
  have hb₂' : b₂ < α-1 := by dsimp [b₂]; linarith only [hα]
  have hbne : b₁-b₂ ≠ 0 := by dsimp [b₁,b₂]; linarith only [hα]
  obtain ⟨l₁,hl₁⟩ := energy_tendsto g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz b₁ hb₁ hb₁'
  obtain ⟨l₂,hl₂⟩ := energy_tendsto g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz b₂ hb₂ hb₂'
  let K := fun t => t*inner ℝ (xd t+β • gradient g (x t)) (x t-z)+(α-1)/2*‖x t-z‖^2
  let L := (l₁-l₂)/(b₁-b₂)
  have hK : Tendsto K atTop (𝓝 L) := by
    have hg0 := scaled_gap_tendsto_zero g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz
    have h := ((hl₁.sub hl₂).div_const (b₁-b₂)).add (hg0.const_mul β)
    simp only [mul_zero,add_zero] at h
    apply h.congr'
    filter_upwards [] with t
    dsimp [K]
    rw [energy_difference]
    field_simp [hbne]
    ring
  let P := fun t => ∫ s in (t₀+1)..t, support g x z s
  let Pinf := ∫ s in Ici (t₀+1), support g x z s
  have hPi := support_integrable g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz
  have hP : Tendsto P atTop (𝓝 Pinf) := primitive_tendsto (t₀+1) (support g x z) hPi
  let u := fun t => ‖x t-z‖^2/2+β*P t
  let u' := fun t => inner ℝ (x t-z) (xd t)+β*support g x z t
  have hu t (ht : t ∈ Ici (t₀+2)) : HasDerivAt u (u' t) t := by
    have htt : t₀+2 ≤ t := ht
    have hx := (((trajectory_deriv hsol (t := t) (by linarith only [htt])).sub_const z).norm_sq).div_const 2
    have hp := (primitive_hasDerivAt (t₀+1) (support g x z)
      ((support_continuous hg hsol z).mono (Ici_subset_Ici.mpr (by linarith))) t
      (by linarith only [htt])).const_mul β
    convert hx.add hp using 1 <;> first | rfl | ring
  have hlim : Tendsto (fun t => (α-1)*u t+t*u' t) atTop (𝓝 (L+β*(α-1)*Pinf)) := by
    apply (hK.add (hP.const_mul (β*(α-1)))).congr'
    filter_upwards [] with t
    dsimp [K,u,u',support]
    rw [inner_add_left,real_inner_smul_left,real_inner_comm (xd t) (x t-z)]
    ring
  have huL := euler_limit (t₀+2) (α-1) (L+β*(α-1)*Pinf)
    (by linarith only [ht₀]) (by linarith only [hα]) u u' hu hlim
  refine ⟨2*((L+β*(α-1)*Pinf)/(α-1)-β*Pinf), ?_⟩
  apply ((huL.sub (hP.const_mul β)).const_mul 2).congr'
  filter_upwards [] with t
  dsimp [u]
  ring
end TikhonovProof

open Filter Topology Set MeasureTheory

namespace TikhonovProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem weak_inner_continuous (v : H) :
    Continuous (fun w : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm w) v) := by
  have he : (fun w : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm w) v) =
      fun w => (innerSL ℝ v) ((toWeakSpace ℝ H).symm w) := by
    funext w
    exact real_inner_comm _ _
  rw [he]
  exact WeakBilin.eval_continuous (topDualPairing ℝ H).flip (innerSL ℝ v)

theorem weak_ball_isCompact (R : ℝ) :
    IsCompact ((toWeakSpace ℝ H) '' Metric.closedBall (0 : H) R) := by
  let f : WeakDual ℝ H → WeakSpace ℝ H := fun l =>
    toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual l))
  have hc : Continuous f := by
    apply WeakBilin.continuous_of_continuous_eval
    intro l
    have he : (fun w : WeakDual ℝ H => l ((toWeakSpace ℝ H).symm (f w))) =
        fun w => w ((InnerProductSpace.toDual ℝ H).symm l) := by
      funext w
      change l ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual w)) =
        (WeakDual.toStrongDual w) ((InnerProductSpace.toDual ℝ H).symm l)
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
    change Continuous (fun w : WeakDual ℝ H => l ((toWeakSpace ℝ H).symm (f w)))
    rw [he]
    exact WeakBilin.eval_continuous (topDualPairing ℝ H) _
  have hk := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R).image hc
  have hi : f '' (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) R) =
      (toWeakSpace ℝ H) '' Metric.closedBall (0 : H) R := by
    ext w
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual l), ?_, rfl⟩
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at hl
      simpa only [Metric.mem_closedBall, dist_zero_right,
        (InnerProductSpace.toDual ℝ H).symm.norm_map] using hl
    · rintro ⟨v, hv, rfl⟩
      refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H v), ?_, ?_⟩
      · simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
        change ‖(InnerProductSpace.toDual ℝ H) v‖ ≤ R
        simpa only [Metric.mem_closedBall, dist_zero_right,
          (InnerProductSpace.toDual ℝ H).norm_map] using hv
      · simp [f]
  rwa [hi] at hk

omit [CompleteSpace H] in
theorem weak_sublevel_closed (g : H → ℝ)
    (hgc : ConvexOn ℝ univ g) (hg : Continuous g) (c : ℝ) :
    IsClosed ((toWeakSpace ℝ H) '' {x : H | g x ≤ c}) := by
  have hs : IsClosed {x : H | g x ≤ c} := isClosed_le hg continuous_const
  have hcv : Convex ℝ {x : H | g x ≤ c} := by
    simpa using hgc.convex_le c
  rw [← closure_eq_iff_isClosed]
  rw [← hcv.toWeakSpace_closure ℝ, hs.closure_eq]

end TikhonovProof

open Filter Topology Set MeasureTheory

namespace TikhonovProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem weak_cluster_minimal (g : H → ℝ) (x : ℝ → H)
    (hgc : ConvexOn ℝ univ g) (hcont : Continuous g)
    (z : H) (hz : z ∈ TikhonovHDD.Weak.argmin g)
    (hgap : Tendsto (gap g x z) atTop (𝓝 0))
    (w : WeakSpace ℝ H) (hw : MapClusterPt w atTop (fun t => toWeakSpace ℝ H (x t))) :
    (toWeakSpace ℝ H).symm w ∈ TikhonovHDD.Weak.argmin g := by
  have hle : g ((toWeakSpace ℝ H).symm w) ≤ g z := by
    by_contra hn
    have hp : 0 < (g ((toWeakSpace ℝ H).symm w) - g z) / 2 := by
      linarith [lt_of_not_ge hn]
    have he := hgap.eventually (gt_mem_nhds hp)
    have hmem : ∀ᶠ t in atTop, toWeakSpace ℝ H (x t) ∈
        (toWeakSpace ℝ H) '' {v : H | g v ≤ g z + (g ((toWeakSpace ℝ H).symm w) - g z) / 2} := by
      filter_upwards [he] with t ht
      refine ⟨x t, ?_, rfl⟩
      change g (x t) ≤ _
      dsimp [gap] at ht
      linarith
    have hm := (weak_sublevel_closed g hgc hcont
      (g z + (g ((toWeakSpace ℝ H).symm w) - g z) / 2)).mem_of_mapClusterPt hw hmem
    obtain ⟨v, hv, hvw⟩ := hm
    have hv' : v = (toWeakSpace ℝ H).symm w := by
      rw [← hvw]
      exact ((toWeakSpace ℝ H).symm_apply_apply v).symm
    rw [hv'] at hv
    change g ((toWeakSpace ℝ H).symm w) ≤ _ at hv
    linarith
  intro y
  exact hle.trans (hz y)

omit [CompleteSpace H] in
theorem weak_cluster_unique (x : ℝ → H) (p q : WeakSpace ℝ H)
    (hp : MapClusterPt p atTop (fun t => toWeakSpace ℝ H (x t)))
    (hq : MapClusterPt q atTop (fun t => toWeakSpace ℝ H (x t)))
    (hlp : ∃ l : ℝ, Tendsto (fun t => ‖x t - (toWeakSpace ℝ H).symm p‖^2) atTop (𝓝 l))
    (hlq : ∃ l : ℝ, Tendsto (fun t => ‖x t - (toWeakSpace ℝ H).symm q‖^2) atTop (𝓝 l)) :
    p = q := by
  let P := (toWeakSpace ℝ H).symm p
  let Q := (toWeakSpace ℝ H).symm q
  obtain ⟨lp, hlp⟩ := hlp
  obtain ⟨lq, hlq⟩ := hlq
  let L : ℝ := (lp - lq - ‖P‖^2 + ‖Q‖^2) / 2
  have he : ∀ t : ℝ, inner ℝ (x t) (Q - P) =
      (‖x t - P‖^2 - ‖x t - Q‖^2 - ‖P‖^2 + ‖Q‖^2) / 2 := by
    intro t
    rw [inner_sub_right, norm_sub_sq_real, norm_sub_sq_real]
    ring
  have ht : Tendsto (fun t => inner ℝ (x t) (Q - P)) atTop (𝓝 L) := by
    simp_rw [he]
    exact (((hlp.sub hlq).sub_const (‖P‖^2)).add_const (‖Q‖^2)).div_const 2
  have hpc := MapClusterPt.continuousAt_comp (weak_inner_continuous (Q - P)).continuousAt hp
  have hqc := MapClusterPt.continuousAt_comp (weak_inner_continuous (Q - P)).continuousAt hq
  have hpL : inner ℝ P (Q - P) = L := by
    apply eq_of_nhds_neBot
    exact ClusterPt.mono hpc ht
  have hqL : inner ℝ Q (Q - P) = L := by
    apply eq_of_nhds_neBot
    exact ClusterPt.mono hqc ht
  have hz : ‖Q - P‖^2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, hqL, hpL, sub_self]
  have hQP : Q = P := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  apply (toWeakSpace ℝ H).symm.injective
  exact hQP.symm

theorem opial_filter (g : H → ℝ) (x : ℝ → H)
    (hgc : ConvexOn ℝ univ g) (hcont : Continuous g)
    (hne : (TikhonovHDD.Weak.argmin g).Nonempty)
    (hbound : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ t in atTop, ‖x t‖ ≤ R)
    (hgap : ∀ z ∈ TikhonovHDD.Weak.argmin g, Tendsto (gap g x z) atTop (𝓝 0))
    (hdist : ∀ z ∈ TikhonovHDD.Weak.argmin g,
      ∃ l : ℝ, Tendsto (fun t => ‖x t - z‖^2) atTop (𝓝 l)) :
    ∃ xbar ∈ TikhonovHDD.Weak.argmin g, TikhonovHDD.Weak.WeakTendstoAtTop x xbar := by
  obtain ⟨R, _, hR⟩ := hbound
  let K := (toWeakSpace ℝ H) '' Metric.closedBall (0 : H) R
  have hK : IsCompact K := weak_ball_isCompact R
  have hmem : ∀ᶠ t in atTop, toWeakSpace ℝ H (x t) ∈ K := by
    filter_upwards [hR] with t ht
    refine ⟨x t, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using ht
  obtain ⟨w, _, hw⟩ := hK.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨z, hz⟩ := hne
  have hmin : ∀ v, MapClusterPt v atTop (fun t => toWeakSpace ℝ H (x t)) →
      (toWeakSpace ℝ H).symm v ∈ TikhonovHDD.Weak.argmin g :=
    fun v hv => weak_cluster_minimal g x hgc hcont z hz (hgap z hz) v hv
  have ht : Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop (𝓝 w) := by
    apply hK.tendsto_nhds_of_unique_mapClusterPt hmem
    intro v _ hv
    exact weak_cluster_unique x v w hv hw
      (hdist _ (hmin v hv)) (hdist _ (hmin w hw))
  refine ⟨(toWeakSpace ℝ H).symm w, hmin w hw, ?_⟩
  intro v
  exact (weak_inner_continuous v).continuousAt.tendsto.comp ht

variable (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ)
  (u₀ v₀ : H) (x xd xdd : ℝ → H)
  (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : TikhonovHDD.Weak.GenAssumptionG g)
  (hε : TikhonovHDD.Weak.GenAssumptionEps t₀ ε ε')
  (hsol : TikhonovHDD.Weak.IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
  (hint : IntegrableOn (fun t => t * ε t) (Ici t₀)) (hα : 3 < α)
include ht₀ hβ hg hε hsol hint hα

theorem weak_converges : ∃ xbar ∈ TikhonovHDD.Weak.argmin g,
    TikhonovHDD.Weak.WeakTendstoAtTop x xbar := by
  apply opial_filter g x hg.1 hg.2.1.continuous hg.2.2.2.2
  · exact trajectory_bounded g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα
  · intro z hz
    exact gap_tendsto_zero g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz
  · intro z hz
    exact distance_squared_limit g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα z hz

end TikhonovProof

open Filter Topology Set MeasureTheory Asymptotics
namespace TikhonovHDD.Weak

theorem theorem_3_5
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : GenAssumptionG g) (hε : GenAssumptionEps t₀ ε ε')
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
    (hint : IntegrableOn (fun t => t * ε t) (Ici t₀))
    (hab : CondA β t₀ ε ε' ∨ CondB t₀ ε)
    (hα : 3 < α) :
    ∃ xbar ∈ argmin g, WeakTendstoAtTop x xbar := by
  have _ := hab
  exact TikhonovProof.weak_converges g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hα

end TikhonovHDD.Weak

open TikhonovHDD.Weak


theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (ε ε' : ℝ → ℝ) (α β t₀ : ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hβ : 0 ≤ β) (hg : GenAssumptionG g) (hε : GenAssumptionEps t₀ ε ε')
    (hsol : IsSolution g ε α β t₀ u₀ v₀ x xd xdd)
    (hint : IntegrableOn (fun t => t * ε t) (Ici t₀))
    (hab : CondA β t₀ ε ε' ∨ CondB t₀ ε)
    (hα : 3 < α) :
    ∃ xbar ∈ argmin g, WeakTendstoAtTop x xbar := by
  exact TikhonovHDD.Weak.theorem_3_5 g ε ε' α β t₀ u₀ v₀ x xd xdd ht₀ hβ hg hε hsol hint hab hα
