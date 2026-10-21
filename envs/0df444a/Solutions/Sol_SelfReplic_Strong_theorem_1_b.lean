-- Prove2me | solution 1 for SelfReplic.Strong.theorem_1_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:45:20.100981+00:00
-- url     : https://prove2.me/submissions/641a811a-228e-4047-8a9f-8ed85b4b476a

import Mathlib
import Definitions.Def_SelfReplic_Strong_Model

open MeasureTheory Set SelfReplic.Strong Filter Topology

namespace SRLib

/-- FTC for a function given in integral form on `[0,T]` with continuous integrand. -/
lemma hasDerivWithinAt_of_integral {F g : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hg : ContinuousOn g (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, F t = c + ∫ u in (0:ℝ)..t, g u) :
    ∀ t ∈ Ico 0 T, HasDerivWithinAt F (g t) (Ici t) t := by
  intro t ht
  set g' : ℝ → ℝ := fun u => g (projIcc 0 T hT u) with hg'
  have hcont : Continuous g' := by
    apply hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    intro u; exact (projIcc 0 T hT u).2
  have heq : ∀ v ∈ Icc 0 T, F v = c + ∫ u in (0:ℝ)..v, g' u := by
    intro v hv
    rw [hF v hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hv.1] at hu
    simp only [hg']
    rw [projIcc_of_mem hT ⟨hu.1, hu.2.trans hv.2⟩]
  have hd : HasDerivAt (fun v => c + ∫ u in (0:ℝ)..v, g' u) (g' t) t := by
    have := hcont.integral_hasStrictDerivAt 0 t
    exact this.hasDerivAt.const_add c
  have hgt : g' t = g t := by
    simp only [hg']; rw [projIcc_of_mem hT ⟨ht.1, ht.2.le⟩]
  rw [← hgt]
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [Ico_mem_nhdsGE ht.2] with v hv
    exact heq v ⟨ht.1.trans hv.1, hv.2.le⟩
  · exact heq t ⟨ht.1, ht.2.le⟩


/-- Grönwall-type sign lemma: `η' ≤ K η⁺`, `η a ≤ 0` imply `η ≤ 0`. -/
lemma nonpos_of_deriv_le_pos_part {η η' : ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hc : ContinuousOn η (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt η (η' x) (Ici x) x)
    (ha : η a ≤ 0) (hb : ∀ x ∈ Ico a b, η' x ≤ K * max (η x) 0) :
    ∀ x ∈ Icc a b, η x ≤ 0 := by
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := fun t => max (η t) 0)
    (f' := fun x => max (η' x) 0) (δ := 0) (K := K) (ε := 0) (a := a) (b := b)
    (continuous_id.max continuous_const |>.comp_continuousOn hc)
    (by
      intro x hx r hr
      have hr0 : 0 < r := lt_of_le_of_lt (le_max_right _ _) hr
      have hr1 : η' x < r := lt_of_le_of_lt (le_max_left _ _) hr
      have ht := (hasDerivWithinAt_iff_tendsto_slope.mp (hd x hx))
      have hset : Ici x \ {x} = Ioi x := by
        ext z; simp [lt_iff_le_and_ne]
      rw [hset] at ht
      have hev : ∀ᶠ z in 𝓝[>] x, slope η x z < r := ht (Iio_mem_nhds hr1)
      apply Eventually.frequently
      filter_upwards [hev, self_mem_nhdsWithin] with z hz hzx
      have hzx' : 0 < z - x := sub_pos.mpr hzx
      rw [slope_def_field] at hz
      have h1 : max (η z) 0 - max (η x) 0 ≤ max (η z - η x) 0 := by
        rcases le_total (η z) 0 with h | h <;> rcases le_total (η x) 0 with h' | h' <;>
          simp [h, h'] <;>
          first | linarith | (apply le_max_of_le_left; linarith) |
            (apply le_max_of_le_right; linarith)
      have h2 : (z - x)⁻¹ * (max (η z) 0 - max (η x) 0) ≤ (z - x)⁻¹ * max (η z - η x) 0 :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hzx'.le)
      have h3 : (z - x)⁻¹ * max (η z - η x) 0 = max ((η z - η x) / (z - x)) 0 := by
        rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hzx'.le), mul_zero, div_eq_inv_mul]
      calc (z - x)⁻¹ * (max (η z) 0 - max (η x) 0) ≤ max ((η z - η x) / (z - x)) 0 := by
            rw [← h3]; exact h2
        _ < r := max_lt hz hr0)
    (by simp [ha])
    (by
      intro x hx
      simp only [add_zero]
      exact max_le (hb x hx) (mul_nonneg hK (le_max_right _ _)))
  intro x hx
  have := key x hx
  rw [gronwallBound_ε0_δ0] at this
  exact (le_max_left _ _).trans this

/-- Integration by parts for two functions in integral form (absolutely continuous). -/
lemma bp2 {f g : ℝ → ℝ} {T G0 : ℝ} (hf : IntervalIntegrable f volume 0 T)
    (hg : IntervalIntegrable g volume 0 T) :
    ∫ t in (0:ℝ)..T, (G0 + ∫ u in (0:ℝ)..t, g u) * f t =
      (G0 + ∫ u in (0:ℝ)..T, g u) * (∫ u in (0:ℝ)..T, f u) -
        ∫ t in (0:ℝ)..T, g t * ∫ u in (0:ℝ)..t, f u := by
  have hGac : AbsolutelyContinuousOnInterval (fun x => G0 + ∫ u in (0:ℝ)..x, g u) 0 T := by
    have h1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => G0) 0 T :=
      (LipschitzWith.const G0).lipschitzOnWith.absolutelyContinuousOnInterval
    have h2 := hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
    exact h1.add h2
  have hFac := hf.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have h := hGac.integral_mul_deriv_eq_deriv_mul hFac
  have hdF := hf.ae_hasDerivAt_integral
  have hdG := hg.ae_hasDerivAt_integral
  have e1 : ∫ t in (0:ℝ)..T, (G0 + ∫ u in (0:ℝ)..t, g u) * f t =
      ∫ t in (0:ℝ)..T, (G0 + ∫ u in (0:ℝ)..t, g u) * deriv (fun x => ∫ u in (0:ℝ)..x, f u) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdF] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI) 0 (by simp)).deriv]
  have e2 : ∫ t in (0:ℝ)..T, g t * ∫ u in (0:ℝ)..t, f u =
      ∫ t in (0:ℝ)..T, deriv (fun x => G0 + ∫ u in (0:ℝ)..x, g u) t * ∫ u in (0:ℝ)..t, f u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdG] with x hx hxI
    rw [((hx (uIoc_subset_uIcc hxI) 0 (by simp)).const_add G0).deriv]
  rw [e1, e2, h]
  simp

lemma continuousOn_of_integral {F g : ℝ → ℝ} {c T : ℝ} (hT : 0 ≤ T)
    (hg : ContinuousOn g (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, F t = c + ∫ u in (0:ℝ)..t, g u) :
    ContinuousOn F (Icc 0 T) := by
  set g' : ℝ → ℝ := fun u => g (projIcc 0 T hT u) with hg'
  have hcont : Continuous g' := by
    apply hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    intro u; exact (projIcc 0 T hT u).2
  have hc2 : Continuous (fun v => c + ∫ u in (0:ℝ)..v, g' u) :=
    continuous_const.add (continuous_iff_continuousAt.2 fun v =>
      (hcont.integral_hasStrictDerivAt 0 v).hasDerivAt.continuousAt)
  apply hc2.continuousOn.congr
  intro v hv
  rw [hF v hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hv.1] at hu
  simp only [hg']
  rw [projIcc_of_mem hT ⟨hu.1, hu.2.trans hv.2⟩]

lemma d_continuousOn (P : Params) (x : Traj) {A : Set ℝ} (hD : ContinuousOn x.D A)
    (hS : ContinuousOn x.S A) : ContinuousOn (x.d P) A := by
  unfold Traj.d demandRate
  exact (continuousOn_const.add ((continuousOn_const.mul hS).div_const _)).mul
    (continuousOn_const.sub hD)

/-- Closed form of the remaining market: `m - D = m exp(-(αt + (β/m)∫S))`. -/
lemma remaining_formula (P : Params) (hm : P.m ≠ 0) (hT : 0 ≤ P.T) (z : Traj)
    (hD : ContinuousOn z.D (Icc 0 P.T)) (hS : ContinuousOn z.S (Icc 0 P.T))
    (hDi : ∀ t ∈ Icc 0 P.T, z.D t = ∫ u in (0:ℝ)..t, z.d P u) :
    ∀ t ∈ Icc 0 P.T, P.m - z.D t =
      P.m * Real.exp (-(P.alpha * t + P.beta / P.m * ∫ u in (0:ℝ)..t, z.S u)) := by
  set Q : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, z.S u with hQ
  have hQi : ∀ t ∈ Icc 0 P.T, Q t = 0 + ∫ u in (0:ℝ)..t, z.S u := fun t _ => by simp [hQ]
  have dQ := hasDerivWithinAt_of_integral hT hS hQi
  have cQ := continuousOn_of_integral hT hS hQi
  have hd := d_continuousOn P z hD hS
  have dD := hasDerivWithinAt_of_integral (F := z.D) hT hd (c := 0) (fun t ht => by rw [zero_add]; exact hDi t ht)
  set E : ℝ → ℝ := fun t => (P.m - z.D t) * Real.exp (P.alpha * t + P.beta / P.m * Q t) with hE
  have cE : ContinuousOn E (Icc 0 P.T) := by
    apply (continuousOn_const.sub hD).mul
    exact Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul cQ))
  have dE : ∀ t ∈ Ico 0 P.T, HasDerivWithinAt E 0 (Ici t) t := by
    intro t ht
    have h1 := ((hasDerivWithinAt_id t _).const_mul P.alpha).add ((dQ t ht).const_mul (P.beta / P.m))
    have h2 := ((hasDerivWithinAt_const t (Ici t) P.m).sub (dD t ht)).mul h1.exp
    have h3 := h2.congr_deriv (g' := (0:ℝ)) (by
      simp only [Pi.sub_apply, Pi.add_apply, id]; unfold Traj.d demandRate; field_simp; ring)
    exact h3
  have hc := constant_of_has_deriv_right_zero cE dE
  intro t ht
  have h := hc t ht
  have hD0 : z.D 0 = 0 := by rw [hDi 0 ⟨le_refl _, hT⟩]; simp
  simp only [hE, hQ, hD0, intervalIntegral.integral_same, mul_zero, add_zero, Real.exp_zero,
    sub_zero, mul_one] at h
  have hpos := Real.exp_pos (P.alpha * t + P.beta / P.m * ∫ u in (0:ℝ)..t, z.S u)
  have h' : P.m - z.D t = P.m / Real.exp (P.alpha * t + P.beta / P.m * ∫ u in (0:ℝ)..t, z.S u) := by
    rw [eq_div_iff hpos.ne']; exact h
  rw [Real.exp_neg, h', div_eq_mul_inv]

lemma ii_of_cont {g : ℝ → ℝ} {T t : ℝ} (hg : ContinuousOn g (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable g volume 0 t :=
  (hg.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

lemma ii_of_int {g : ℝ → ℝ} {T t : ℝ} (hg : IntegrableOn g (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable g volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
    (hg.mono_set (Icc_subset_Icc le_rfl ht.2))

/-- Comparison: the cumulative demand of any admissible trajectory never exceeds that of the
sales-always-on trajectory. -/
lemma demand_le (P : Params) (hP : P.Standing) (x y : Traj)
    (hxD : ContinuousOn x.D (Icc 0 P.T)) (hxS : ContinuousOn x.S (Icc 0 P.T))
    (hx : ∀ t ∈ Icc 0 P.T, x.D t = ∫ u in (0:ℝ)..t, x.d P u ∧
        x.S t = ∫ u in (0:ℝ)..t, (x.d P u - P.w * x.S u))
    (hyD : ContinuousOn y.D (Icc 0 P.T)) (hyS : ContinuousOn y.S (Icc 0 P.T))
    (hysi : IntegrableOn y.s (Icc 0 P.T))
    (hy : ∀ t ∈ Icc 0 P.T, y.D t = ∫ u in (0:ℝ)..t, y.d P u ∧
        y.S t = ∫ u in (0:ℝ)..t, (y.s u - P.w * y.S u))
    (hsd : ∀ t ∈ Icc 0 P.T, y.s t ≤ y.d P t) :
    ∀ t ∈ Icc 0 P.T, y.D t ≤ x.D t := by
  have hm : 0 < P.m := hP.2.2.2.2.2.1
  have hT : 0 < P.T := hP.2.2.2.2.2.2.1
  have hβ : 0 ≤ P.beta := hP.2.2.2.2.2.2.2.2.1
  have hk : 0 ≤ P.beta / P.m := div_nonneg hβ hm.le
  set k := P.beta / P.m with hkdef
  set Qx : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, x.S u with hQx
  set Qy : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, y.S u with hQy
  have hxd := d_continuousOn P x hxD hxS
  have hyd := d_continuousOn P y hyD hyS
  -- structural identities
  have Sx_eq : ∀ t ∈ Icc 0 P.T, x.S t = x.D t - P.w * Qx t := by
    intro t ht
    rw [(hx t ht).2, (hx t ht).1, intervalIntegral.integral_sub (ii_of_cont hxd ht)
      ((ii_of_cont hxS ht).const_mul _), intervalIntegral.integral_const_mul]
  set W : ℝ → ℝ := fun t => (∫ u in (0:ℝ)..t, y.d P u) - ∫ u in (0:ℝ)..t, y.s u with hW
  have Sy_eq : ∀ t ∈ Icc 0 P.T, y.S t = y.D t - P.w * Qy t - W t := by
    intro t ht
    rw [(hy t ht).2, (hy t ht).1, intervalIntegral.integral_sub (ii_of_int hysi ht)
      ((ii_of_cont hyS ht).const_mul _), intervalIntegral.integral_const_mul]
    simp only [hW, hQy]; ring
  have W_nn : ∀ t ∈ Icc 0 P.T, 0 ≤ W t := by
    intro t ht
    simp only [hW, sub_nonneg]
    exact intervalIntegral.integral_mono_on ht.1 (ii_of_int hysi ht) (ii_of_cont hyd ht)
      (fun u hu => hsd u ⟨hu.1, hu.2.trans ht.2⟩)
  have Rx := remaining_formula P hm.ne' hT.le x hxD hxS (fun t ht => (hx t ht).1)
  have Ry := remaining_formula P hm.ne' hT.le y hyD hyS (fun t ht => (hy t ht).1)
  have hRel : ∀ t ∈ Icc 0 P.T, y.D t - x.D t =
      (P.m - x.D t) * (1 - Real.exp (-(k * (Qy t - Qx t)))) := by
    intro t ht
    have e1 := Rx t ht
    have e2 := Ry t ht
    have : P.m - y.D t = (P.m - x.D t) * Real.exp (-(k * (Qy t - Qx t))) := by
      rw [e1, e2, mul_assoc, ← Real.exp_add]
      congr 2
      simp only [hQx, hQy, hkdef]; ring
    linarith
  have Rx_pos : ∀ t ∈ Icc 0 P.T, 0 < P.m - x.D t := by
    intro t ht; rw [Rx t ht]; positivity
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_const.sub hxD)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_refl _, hT.le⟩)
  -- derivatives
  have hQxi : ∀ t ∈ Icc 0 P.T, Qx t = 0 + ∫ u in (0:ℝ)..t, x.S u := fun t _ => by simp [hQx]
  have hQyi : ∀ t ∈ Icc 0 P.T, Qy t = 0 + ∫ u in (0:ℝ)..t, y.S u := fun t _ => by simp [hQy]
  have dQx := hasDerivWithinAt_of_integral hT.le hxS hQxi
  have dQy := hasDerivWithinAt_of_integral hT.le hyS hQyi
  have cQx := continuousOn_of_integral hT.le hxS hQxi
  have cQy := continuousOn_of_integral hT.le hyS hQyi
  set η : ℝ → ℝ := fun t => Real.exp (P.w * t) * (Qy t - Qx t) with hη
  have cη : ContinuousOn η (Icc 0 P.T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul (cQy.sub cQx)
  have dη : ∀ t ∈ Ico 0 P.T, HasDerivWithinAt η
      (Real.exp (P.w * t) * (y.D t - x.D t - W t)) (Ici t) t := by
    intro t ht
    have htI : t ∈ Icc 0 P.T := ⟨ht.1, ht.2.le⟩
    have h1 : HasDerivWithinAt (fun t => Real.exp (P.w * t)) (Real.exp (P.w * t) * (P.w * 1))
        (Ici t) t := (((hasDerivAt_id t).const_mul P.w).exp).hasDerivWithinAt
    have h2 := h1.mul ((dQy t ht).sub (dQx t ht))
    apply h2.congr_deriv
    rw [Sx_eq t htI, Sy_eq t htI]; simp only [Pi.sub_apply]; ring
  have hbound : ∀ t ∈ Ico 0 P.T, Real.exp (P.w * t) * (y.D t - x.D t - W t) ≤
      (B * k) * max (η t) 0 := by
    intro t ht
    have htI : t ∈ Icc 0 P.T := ⟨ht.1, ht.2.le⟩
    have hexp := Real.exp_pos (P.w * t)
    set ζ := Qy t - Qx t
    have h1 : 1 - Real.exp (-(k * ζ)) ≤ k * max ζ 0 := by
      rcases le_total ζ 0 with h | h
      · rw [max_eq_right h, mul_zero, sub_nonpos]
        apply Real.one_le_exp; nlinarith
      · rw [max_eq_left h]
        have := Real.add_one_le_exp (-(k * ζ)); linarith
    have hRx := Rx_pos t htI
    have hRB : P.m - x.D t ≤ B := by
      have := hB t htI; rw [Real.norm_eq_abs] at this; exact (le_abs_self _).trans this
    have hkm : 0 ≤ k * max ζ 0 := mul_nonneg hk (le_max_right _ _)
    calc Real.exp (P.w * t) * (y.D t - x.D t - W t)
        ≤ Real.exp (P.w * t) * (y.D t - x.D t) :=
          mul_le_mul_of_nonneg_left (by linarith [W_nn t htI]) hexp.le
      _ = Real.exp (P.w * t) * ((P.m - x.D t) * (1 - Real.exp (-(k * ζ)))) := by
          rw [hRel t htI]
      _ ≤ Real.exp (P.w * t) * ((P.m - x.D t) * (k * max ζ 0)) := by gcongr
      _ ≤ Real.exp (P.w * t) * (B * (k * max ζ 0)) := by gcongr
      _ = (B * k) * max (Real.exp (P.w * t) * ζ) 0 := by
          rw [show Real.exp (P.w * t) * (B * (k * max ζ 0)) =
            B * k * (Real.exp (P.w * t) * max ζ 0) by ring, mul_max_of_nonneg _ _ hexp.le,
            mul_zero]
  have hη0 : η 0 ≤ 0 := by simp [hη, hQx, hQy]
  have hneg := nonpos_of_deriv_le_pos_part (mul_nonneg hB0 hk) cη dη hη0 hbound
  intro t ht
  have h1 := hneg t ht
  have hζ : Qy t - Qx t ≤ 0 := by
    have hexp := Real.exp_pos (P.w * t)
    simp only [hη] at h1
    by_contra hc; rw [not_le] at hc
    have := mul_pos hexp hc; linarith
  have h2 : 1 ≤ Real.exp (-(k * (Qy t - Qx t))) := Real.one_le_exp (by nlinarith)
  have h3 := hRel t ht
  have h4 := Rx_pos t ht
  nlinarith

lemma withIL_d (P : Params) (J : ℝ) (x : Traj) : x.d (P.withIL J) = x.d P := rfl

lemma salesOn_form (P : Params) (J : ℝ) (x : Traj) (hx : IsAdmissible (P.withIL J) x)
    (hs : SalesAlwaysOn (P.withIL J) x) :
    ∀ t ∈ Icc 0 P.T, x.D t = 0 + ∫ u in (0:ℝ)..t, x.d P u ∧
        x.S t = 0 + ∫ u in (0:ℝ)..t, (x.d P u - P.w * x.S u) := by
  intro t ht
  obtain ⟨-, -, -, -, -, hode, -⟩ := hx
  obtain ⟨h1, h2, -⟩ := hode t ht
  refine ⟨by rw [zero_add]; exact h1, ?_⟩
  rw [zero_add, h2]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht.1] at hu
  simp only
  rw [hs u ⟨hu.1, hu.2.trans ht.2⟩]
  rfl

lemma key_lip (a b m Sx Sy Dx Dy B N : ℝ) (hSx : |Sx| ≤ B) (hDy : |Dy| ≤ B)
    (hN1 : |Dx - Dy| ≤ N) (hN2 : |Sx - Sy| ≤ N) :
    |(a + b * Sx / m) * (m - Dx) - (a + b * Sy / m) * (m - Dy)| ≤
      (|a| + |b / m| * B + |b / m| * (|m| + B)) * N := by
  have hN : 0 ≤ N := (abs_nonneg _).trans hN1
  have hB : 0 ≤ B := (abs_nonneg _).trans hSx
  have hab : 0 ≤ |a| + |b / m| * B := by positivity
  have h1 : |a + b / m * Sx| ≤ |a| + |b / m| * B := by
    calc |a + b / m * Sx| ≤ |a| + |b / m * Sx| := abs_add_le _ _
      _ = |a| + |b / m| * |Sx| := by rw [abs_mul]
      _ ≤ |a| + |b / m| * B := by gcongr
  have h2 : |m - Dy| ≤ |m| + B := (abs_sub _ _).trans (by gcongr)
  have h3 : |Dy - Dx| ≤ N := by rw [abs_sub_comm]; exact hN1
  calc |(a + b * Sx / m) * (m - Dx) - (a + b * Sy / m) * (m - Dy)|
      = |(a + b / m * Sx) * (Dy - Dx) + b / m * (Sx - Sy) * (m - Dy)| := by
        congr 1; ring
    _ ≤ |a + b / m * Sx| * |Dy - Dx| + |b / m| * |Sx - Sy| * |m - Dy| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (|a| + |b / m| * B) * N + |b / m| * N * (|m| + B) := by gcongr
    _ = (|a| + |b / m| * B + |b / m| * (|m| + B)) * N := by ring

/-- Uniqueness for the sales-always-on demand system `D' = d`, `S' = d - wS`. -/
lemma salesOn_unique (P : Params) (hT : 0 ≤ P.T) (x y : Traj)
    (hxD : ContinuousOn x.D (Icc 0 P.T)) (hxS : ContinuousOn x.S (Icc 0 P.T))
    (hyD : ContinuousOn y.D (Icc 0 P.T)) (hyS : ContinuousOn y.S (Icc 0 P.T))
    (hx : ∀ t ∈ Icc 0 P.T, x.D t = 0 + ∫ u in (0:ℝ)..t, x.d P u ∧
        x.S t = 0 + ∫ u in (0:ℝ)..t, (x.d P u - P.w * x.S u))
    (hy : ∀ t ∈ Icc 0 P.T, y.D t = 0 + ∫ u in (0:ℝ)..t, y.d P u ∧
        y.S t = 0 + ∫ u in (0:ℝ)..t, (y.d P u - P.w * y.S u)) :
    ∀ t ∈ Icc 0 P.T, x.D t = y.D t ∧ x.S t = y.S t := by
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn hxS
  obtain ⟨B2, hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn hyD
  set B := max B1 B2
  set L := |P.alpha| + |P.beta / P.m| * B + |P.beta / P.m| * (|P.m| + B)
  have hxd := d_continuousOn P x hxD hxS
  have hyd := d_continuousOn P y hyD hyS
  have dxD := hasDerivWithinAt_of_integral hT hxd (fun t ht => (hx t ht).1)
  have dxS := hasDerivWithinAt_of_integral hT (hxd.sub (continuousOn_const.mul hxS))
    (fun t ht => (hx t ht).2)
  have dyD := hasDerivWithinAt_of_integral hT hyd (fun t ht => (hy t ht).1)
  have dyS := hasDerivWithinAt_of_integral hT (hyd.sub (continuousOn_const.mul hyS))
    (fun t ht => (hy t ht).2)
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => (x.D t - y.D t, x.S t - y.S t))
    (f' := fun t => (x.d P t - y.d P t, (x.d P t - P.w * x.S t) - (y.d P t - P.w * y.S t)))
    (K := L + |P.w|) (a := 0) (b := P.T)
    ((hxD.sub hyD).prodMk (hxS.sub hyS))
    (fun t ht => ((dxD t ht).sub (dyD t ht)).prodMk ((dxS t ht).sub (dyS t ht)))
    (by
      have h0 := hx 0 ⟨le_refl _, hT⟩
      have h0' := hy 0 ⟨le_refl _, hT⟩
      simp only [intervalIntegral.integral_same, add_zero] at h0 h0'
      simp [h0.1, h0.2, h0'.1, h0'.2])
    (by
      intro t ht
      have htI : t ∈ Icc 0 P.T := ⟨ht.1, ht.2.le⟩
      have hSx : |x.S t| ≤ B := by
        have := hB1 t htI; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
      have hDy : |y.D t| ≤ B := by
        have := hB2 t htI; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
      set N := ‖(x.D t - y.D t, x.S t - y.S t)‖
      have hN1 : |x.D t - y.D t| ≤ N := by
        simp only [N, Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
      have hN2 : |x.S t - y.S t| ≤ N := by
        simp only [N, Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _
      have hN : 0 ≤ N := norm_nonneg _
      have hk := key_lip P.alpha P.beta P.m (x.S t) (y.S t) (x.D t) (y.D t) B N hSx hDy hN1 hN2
      have hk' : |x.d P t - y.d P t| ≤ L * N := hk
      have hB0 : 0 ≤ B := (abs_nonneg _).trans hSx
      have hL : 0 ≤ L := by positivity
      simp only [Prod.norm_def, Real.norm_eq_abs]
      apply max_le
      · nlinarith [abs_nonneg P.w]
      · calc |x.d P t - P.w * x.S t - (y.d P t - P.w * y.S t)|
            = |(x.d P t - y.d P t) - P.w * (x.S t - y.S t)| := by ring_nf
          _ ≤ |x.d P t - y.d P t| + |P.w * (x.S t - y.S t)| := abs_sub _ _
          _ ≤ L * N + |P.w| * N := by rw [abs_mul]; gcongr
          _ = (L + |P.w|) * N := by ring)
  intro t ht
  have := hz t ht
  simp only [Prod.mk_eq_zero, sub_eq_zero] at this
  exact this

lemma exp_form (ρ t : ℝ) :
    Real.exp (-(ρ * t)) = 1 + ∫ u in (0:ℝ)..t, (-ρ * Real.exp (-(ρ * u))) := by
  have h : ∀ u ∈ uIcc 0 t, HasDerivAt (fun u => Real.exp (-(ρ * u)))
      (-ρ * Real.exp (-(ρ * u))) u := by
    intro u _
    have h0 : HasDerivAt (fun u => -(ρ * u)) (-ρ) u :=
      (((hasDerivAt_id' u).const_mul ρ).neg).congr_deriv (by ring)
    have := h0.exp
    convert this using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((by fun_prop : Continuous fun u => -ρ * Real.exp (-(ρ * u))).intervalIntegrable _ _)]
  simp

end SRLib


open MeasureTheory Set SelfReplic.Strong Filter Topology

namespace SRLib

lemma primitive_continuousOn {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) :
    ContinuousOn (fun t => ∫ u in (0:ℝ)..t, f u) (Icc 0 T) := by
  have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
    (μ := volume) (f := f)
    (by rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hf)
  rwa [uIcc_of_le hT] at this

/-- A nonincreasing, nonnegative-at-`T` weight preserves the order of cumulative flows. -/
lemma weighted_le {f1 f2 g' : ℝ → ℝ} {T G0 : ℝ} (hT : 0 ≤ T)
    (hf1 : IntervalIntegrable f1 volume 0 T) (hf2 : IntervalIntegrable f2 volume 0 T)
    (hg' : IntervalIntegrable g' volume 0 T) (hneg : ∀ u ∈ Icc 0 T, g' u ≤ 0)
    (hGT : 0 ≤ G0 + ∫ u in (0:ℝ)..T, g' u)
    (hle : ∀ t ∈ Icc 0 T, ∫ u in (0:ℝ)..t, f1 u ≤ ∫ u in (0:ℝ)..t, f2 u) :
    ∫ t in (0:ℝ)..T, (G0 + ∫ u in (0:ℝ)..t, g' u) * f1 t ≤
      ∫ t in (0:ℝ)..T, (G0 + ∫ u in (0:ℝ)..t, g' u) * f2 t := by
  rw [bp2 hf1 hg', bp2 hf2 hg']
  have hc1 := primitive_continuousOn hT hf1
  have hc2 := primitive_continuousOn hT hf2
  have hm : ∫ t in (0:ℝ)..T, g' t * ∫ u in (0:ℝ)..t, f2 u ≤
      ∫ t in (0:ℝ)..T, g' t * ∫ u in (0:ℝ)..t, f1 u := by
    apply intervalIntegral.integral_mono_on hT
    · exact hg'.mul_continuousOn (by rw [uIcc_of_le hT]; exact hc2)
    · exact hg'.mul_continuousOn (by rw [uIcc_of_le hT]; exact hc1)
    · intro t ht
      exact mul_le_mul_of_nonpos_left (hle t ht) (hneg t ht)
  have h1 := hle T ⟨hT, le_refl _⟩
  nlinarith

/-- Profit decomposition along a multiplier `φ = φ0 + ∫ ψ` for the inventory equation. -/
lemma profit_identity (P : Params) (z : Traj) (hz : IsAdmissible P z) (hT : 0 ≤ P.T)
    (ψ : ℝ → ℝ) (φ0 : ℝ) (hψ : IntervalIntegrable ψ volume 0 P.T) :
    profit P z =
      (∫ t in (0:ℝ)..P.T, (P.price * Real.exp (-(P.rho * t)) - (φ0 + ∫ u in (0:ℝ)..t, ψ u)) * z.s t)
      + (∫ t in (0:ℝ)..P.T, (((φ0 + ∫ u in (0:ℝ)..t, ψ u) - P.c * Real.exp (-(P.rho * t))) * z.p t
          + (ψ t - P.h * Real.exp (-(P.rho * t))) * z.I t))
      - (φ0 + ∫ u in (0:ℝ)..P.T, ψ u) * z.I P.T + φ0 * P.IL := by
  obtain ⟨hpi, hsi, -, -, hI, hode, -, -⟩ := hz
  have hpii : IntervalIntegrable z.p volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hpi
  have hsii : IntervalIntegrable z.s volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hsi
  set φ : ℝ → ℝ := fun t => φ0 + ∫ u in (0:ℝ)..t, ψ u with hφ
  set E : ℝ → ℝ := fun t => Real.exp (-(P.rho * t)) with hE
  have hEc : Continuous E := by fun_prop
  have hφc : ContinuousOn φ (uIcc 0 P.T) := by
    rw [uIcc_of_le hT]; exact continuousOn_const.add (primitive_continuousOn hT hψ)
  have hIc : ContinuousOn z.I (uIcc 0 P.T) := by rw [uIcc_of_le hT]; exact hI
  -- integration by parts for the inventory
  have hbp := bp2 (G0 := φ0) (hpii.sub hsii) hψ
  have hIform : ∀ t ∈ uIcc 0 P.T, ψ t * ∫ u in (0:ℝ)..t, (z.p u - z.s u) =
      ψ t * z.I t - P.IL * ψ t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have := (hode t ht).2.2
    rw [show ∫ u in (0:ℝ)..t, (z.p u - z.s u) = z.I t - P.IL by linarith]
    ring
  rw [intervalIntegral.integral_congr hIform, intervalIntegral.integral_sub (hψ.mul_continuousOn hIc)
    (hψ.const_mul _), intervalIntegral.integral_const_mul] at hbp
  have hT' := (hode P.T ⟨hT, le_refl _⟩).2.2
  -- (*) : ∫ φ (p - s) + ∫ ψ I = φ(T) I(T) - φ0 IL
  have hstar : (∫ t in (0:ℝ)..P.T, φ t * (z.p t - z.s t)) + ∫ t in (0:ℝ)..P.T, ψ t * z.I t =
      φ P.T * z.I P.T - φ0 * P.IL := by
    simp only [hφ] at hbp ⊢
    rw [hbp]
    rw [show ∫ u in (0:ℝ)..P.T, (z.p u - z.s u) = z.I P.T - P.IL by linarith]
    ring
  -- split the profit
  have hA : IntervalIntegrable (fun t => (P.price * E t - φ t) * z.s t) volume 0 P.T :=
    hsii.continuousOn_mul ((continuousOn_const.mul hEc.continuousOn).sub hφc)
  have hB : IntervalIntegrable (fun t => (φ t - P.c * E t) * z.p t + (ψ t - P.h * E t) * z.I t)
      volume 0 P.T := by
    apply IntervalIntegrable.add
    · exact hpii.continuousOn_mul (hφc.sub (continuousOn_const.mul hEc.continuousOn))
    · have h1 : IntervalIntegrable (fun t => ψ t * z.I t) volume 0 P.T := hψ.mul_continuousOn hIc
      have h2 : IntervalIntegrable (fun t => P.h * E t * z.I t) volume 0 P.T :=
        ((continuousOn_const.mul hEc.continuousOn).mul hIc).intervalIntegrable
      exact (h1.sub h2).congr (fun t _ => by ring)
  have hC : IntervalIntegrable (fun t => φ t * (z.p t - z.s t)) volume 0 P.T :=
    (hpii.sub hsii).continuousOn_mul hφc
  have hD : IntervalIntegrable (fun t => ψ t * z.I t) volume 0 P.T := hψ.mul_continuousOn hIc
  have hprof : profit P z = ∫ t in (0:ℝ)..P.T,
      ((P.price * E t - φ t) * z.s t + ((φ t - P.c * E t) * z.p t + (ψ t - P.h * E t) * z.I t)
        - (φ t * (z.p t - z.s t) + ψ t * z.I t)) := by
    unfold profit
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hE]; ring
  rw [hprof, intervalIntegral.integral_sub (hA.add hB) (hC.add hD),
    intervalIntegral.integral_add hA hB, intervalIntegral.integral_add hC hD, hstar]
  simp only [hφ, hE]; ring

end SRLib


open MeasureTheory Set SelfReplic.Strong Filter Topology

namespace SRLib

/-- Optimality of a "sales always on, production on from `tp`, depleted at `T`" trajectory,
given that its cumulative sales dominate those of every admissible trajectory. -/
lemma b_optimal (P : Params) (hP : P.Standing) (hSR : P.StrongRepl) (x : Traj)
    (hxa : IsAdmissible P x) (tp : ℝ) (htp : tp ∈ Icc 0 P.T)
    (hxp : ProdOnFrom P x tp) (hxIT : x.I P.T = 0)
    (hcmp : ∀ y : Traj, IsAdmissible P y → ∀ t ∈ Icc 0 P.T,
      ∫ u in (0:ℝ)..t, y.s u ≤ ∫ u in (0:ℝ)..t, x.s u) :
    ∀ y : Traj, IsAdmissible P y → profit P y ≤ profit P x := by
  intro y hya
  have hT : 0 < P.T := hP.2.2.2.2.2.2.1
  have hρ : 0 ≤ P.rho := hP.2.2.2.1
  have hc : 0 ≤ P.c := hP.2.2.2.2.2.2.2.2.2.1
  have hh : 0 ≤ P.h := hP.2.2.2.2.2.2.2.2.2.2
  have hκ : 0 < P.r - P.rho := by linarith [hP.2.2.1]
  have hr : 0 < P.r := by linarith [hP.2.2.1, hP.2.2.2.1]
  have hSR' : P.c * P.r + P.h < (P.r - P.rho) * P.price := hSR
  set κ := P.r - P.rho with hκdef
  set ls := (P.r * P.c + P.h) / κ with hls
  have hlsκ : ls * κ = P.r * P.c + P.h := by rw [hls]; field_simp
  have hls_c : P.c ≤ ls := by
    rw [hls, le_div_iff₀ hκ]; nlinarith
  have hls_pi : ls < P.price := by
    rw [hls, div_lt_iff₀ hκ]; nlinarith
  have hls_r : P.r * ls ≤ P.rho * P.price + P.r * P.c + P.h := by
    have : P.r * ls * κ ≤ (P.rho * P.price + P.r * P.c + P.h) * κ := by
      rw [mul_assoc, hlsκ]; nlinarith
    exact le_of_mul_le_mul_right this hκ
  set E : ℝ → ℝ := fun t => Real.exp (-(P.rho * t)) with hE
  have hEc : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  set lam : ℝ → ℝ := fun t => ls + (P.c - ls) * Real.exp (-(κ * (t - tp))) with hlam
  have lam_bounds : ∀ t, tp ≤ t → P.c ≤ lam t ∧ lam t ≤ ls := by
    intro t ht
    have h1 : Real.exp (-(κ * (t - tp))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 := Real.exp_pos (-(κ * (t - tp)))
    simp only [hlam]
    constructor <;> nlinarith
  set ψ2 : ℝ → ℝ := fun t => E t * (P.r * P.c + P.h - P.r * lam t) with hψ2
  set ψ : ℝ → ℝ := fun t => if t < tp then P.h * E t else ψ2 t with hψ
  have hψ2c : Continuous ψ2 := by simp only [hψ2, hlam, hE]; fun_prop
  -- integrability of ψ
  have hψi : ∀ a b : ℝ, IntervalIntegrable ψ volume a b := by
    intro a b
    have hform : ψ = fun t => P.h * E t + (Ici tp).indicator (fun t => ψ2 t - P.h * E t) t := by
      funext t
      by_cases h : t < tp
      · have : t ∉ Ici tp := fun h' => (not_le.mpr h) h'
        simp [hψ, h, this]
      · have : t ∈ Ici tp := not_lt.mp h
        simp [hψ, h, this]
    rw [hform]
    apply IntervalIntegrable.add
    · exact (continuous_const.mul hEc).intervalIntegrable _ _
    · have hB : IntervalIntegrable (fun t => ψ2 t - P.h * E t) volume a b :=
        (hψ2c.sub (continuous_const.mul hEc)).intervalIntegrable _ _
      exact ⟨hB.1.indicator measurableSet_Ici, hB.2.indicator measurableSet_Ici⟩
  set φ0 := P.c * E tp - ∫ u in (0:ℝ)..tp, ψ u with hφ0
  set φ : ℝ → ℝ := fun t => φ0 + ∫ u in (0:ℝ)..t, ψ u with hφ
  -- φ before tp
  have hφ_lt : ∀ t ∈ Icc 0 P.T, t < tp → φ t ≤ P.c * E t := by
    intro t ht htt
    have hsplit := intervalIntegral.integral_interval_sub_left (hψi 0 tp) (hψi 0 t)
    have hnn : 0 ≤ ∫ u in t..tp, ψ u := by
      apply intervalIntegral.integral_nonneg htt.le
      intro u hu
      simp only [hψ]
      split_ifs with h
      · exact mul_nonneg hh (hEpos u).le
      · have hu' : u = tp := le_antisymm hu.2 (not_lt.mp h)
        have : lam u = P.c := by simp [hlam, hu']
        simp only [hψ2, this]
        nlinarith [hEpos u]
    have hEle : E tp ≤ E t := by
      simp only [hE]; exact Real.exp_le_exp.mpr (by nlinarith)
    simp only [hφ, hφ0]
    nlinarith
  -- φ after tp
  have hΛ : ∀ u, HasDerivAt (fun t => E t * lam t) (ψ2 u) u := by
    intro u
    have h1 : HasDerivAt E (-P.rho * E u) u := by
      have h0 : HasDerivAt (fun u => -(P.rho * u)) (-P.rho) u :=
        (((hasDerivAt_id' u).const_mul P.rho).neg).congr_deriv (by ring)
      exact (h0.exp).congr_deriv (by simp only [hE]; ring)
    have h2 : HasDerivAt lam ((P.c - ls) * (Real.exp (-(κ * (u - tp))) * -κ)) u := by
      have h0 : HasDerivAt (fun u => -(κ * (u - tp))) (-κ) u :=
        ((((hasDerivAt_id' u).sub_const tp).const_mul κ).neg).congr_deriv (by ring)
      exact ((h0.exp).const_mul (P.c - ls)).const_add ls
    have h3 := h1.mul h2
    apply h3.congr_deriv
    simp only [hψ2, hlam]
    linear_combination (E u) * hlsκ
  have hφ_ge : ∀ t ∈ Icc 0 P.T, tp ≤ t → φ t = E t * lam t := by
    intro t ht htt
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hψi 0 tp) (hψi tp t)
    have hcongr : ∫ u in tp..t, ψ u = ∫ u in tp..t, ψ2 u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le htt] at hu
      simp only [hψ, not_lt.mpr hu.1, if_false]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hΛ u)
      (hψ2c.intervalIntegrable tp t)
    have hlt : lam tp = P.c := by simp [hlam]
    simp only [hφ, hφ0]
    rw [← hadd, hcongr, hftc, hlt]
    ring
  -- the weight g = πE - φ in integral form
  set g' : ℝ → ℝ := fun u => -P.rho * P.price * E u - ψ u with hg'
  have hg'i : IntervalIntegrable g' volume 0 P.T :=
    ((continuous_const.mul hEc).intervalIntegrable _ _).sub (hψi 0 P.T)
  have hgform : ∀ t, P.price * E t - φ t = (P.price - φ0) + ∫ u in (0:ℝ)..t, g' u := by
    intro t
    have he := exp_form P.rho t
    simp only [hg', hφ, hE]
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun u =>
      -P.rho * P.price * Real.exp (-(P.rho * u))).intervalIntegrable _ _) (hψi 0 t)]
    have : ∫ u in (0:ℝ)..t, -P.rho * P.price * Real.exp (-(P.rho * u)) =
        P.price * ∫ u in (0:ℝ)..t, -P.rho * Real.exp (-(P.rho * u)) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; ext u; ring
    rw [this, he]; ring
  have hg'neg : ∀ u ∈ Icc 0 P.T, g' u ≤ 0 := by
    intro u hu
    simp only [hg', hψ]
    split_ifs with h
    · have hπ : 0 ≤ P.price := by linarith [hP.2.1]
      nlinarith [mul_nonneg (mul_nonneg hρ hπ) (hEpos u).le, mul_nonneg hh (hEpos u).le]
    · have hb := lam_bounds u (not_lt.mp h)
      simp only [hψ2]
      have h3 : P.r * lam u ≤ P.rho * P.price + P.r * P.c + P.h :=
        (mul_le_mul_of_nonneg_left hb.2 hr.le).trans hls_r
      nlinarith [mul_nonneg (hEpos u).le (sub_nonneg.2 h3)]
  have hTm : P.T ∈ Icc 0 P.T := ⟨hT.le, le_refl _⟩
  have hgT : 0 ≤ (P.price - φ0) + ∫ u in (0:ℝ)..P.T, g' u := by
    rw [← hgform, hφ_ge P.T hTm htp.2]
    have hb := lam_bounds P.T htp.2
    nlinarith [hEpos P.T]
  have hφT : 0 ≤ φ P.T := by
    rw [hφ_ge P.T hTm htp.2]
    have hb := lam_bounds P.T htp.2
    nlinarith [hEpos P.T]
  -- the two profit identities
  have idy := profit_identity P y hya hT.le ψ φ0 (hψi 0 P.T)
  have idx := profit_identity P x hxa hT.le ψ φ0 (hψi 0 P.T)
  -- Q pointwise
  have hQ : ∀ z : Traj, IsAdmissible P z → ∀ t ∈ Icc 0 P.T,
      (φ t - P.c * E t) * z.p t + (ψ t - P.h * E t) * z.I t ≤ 0 := by
    intro z hz t ht
    obtain ⟨-, -, -, -, -, -, hcon, -⟩ := hz
    have hc1 := hcon t ht
    by_cases h : t < tp
    · have h1 := hφ_lt t ht h
      have h2 : ψ t = P.h * E t := by simp [hψ, h]
      rw [h2, sub_self, zero_mul, add_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hc1.1
    · have h1 := hφ_ge t ht (not_lt.mp h)
      have h2 : ψ t = ψ2 t := by simp [hψ, h]
      have hb := lam_bounds t (not_lt.mp h)
      rw [h1, h2]
      simp only [hψ2]
      have he := hEpos t
      have hnn : 0 ≤ E t * lam t - P.c * E t := by nlinarith
      have : (E t * lam t - P.c * E t) * z.p t ≤ (E t * lam t - P.c * E t) * (P.r * z.I t) :=
        mul_le_mul_of_nonneg_left hc1.2.1 hnn
      have key : (E t * lam t - P.c * E t) * z.p t +
          (E t * (P.r * P.c + P.h - P.r * lam t) - P.h * E t) * z.I t =
          (E t * lam t - P.c * E t) * z.p t - (E t * lam t - P.c * E t) * (P.r * z.I t) := by ring
      rw [key]; linarith
  have hQx : ∀ t ∈ Icc 0 P.T,
      (φ t - P.c * E t) * x.p t + (ψ t - P.h * E t) * x.I t = 0 := by
    intro t ht
    rw [hxp t ht]
    by_cases h : t < tp
    · have h2 : ψ t = P.h * E t := by simp [hψ, h]
      simp [h, h2]
    · have h1 := hφ_ge t ht (not_lt.mp h)
      have h2 : ψ t = ψ2 t := by simp [hψ, h]
      simp only [h, if_false, h1, h2, hψ2]
      ring
  have hφc : ContinuousOn φ (uIcc 0 P.T) := by
    rw [uIcc_of_le hT.le]; exact continuousOn_const.add (primitive_continuousOn hT.le (hψi 0 P.T))
  have hQint : ∀ z : Traj, IsAdmissible P z → IntervalIntegrable
      (fun t => (φ t - P.c * E t) * z.p t + (ψ t - P.h * E t) * z.I t) volume 0 P.T := by
    intro z hz
    obtain ⟨hpi, -, -, -, hI, -, -, -⟩ := hz
    have hpii : IntervalIntegrable z.p volume 0 P.T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hpi
    have hIc : ContinuousOn z.I (uIcc 0 P.T) := by rw [uIcc_of_le hT.le]; exact hI
    apply IntervalIntegrable.add
    · exact hpii.continuousOn_mul (hφc.sub (continuousOn_const.mul hEc.continuousOn))
    · have h1 : IntervalIntegrable (fun t => ψ t * z.I t) volume 0 P.T :=
        (hψi 0 P.T).mul_continuousOn hIc
      have h2 : IntervalIntegrable (fun t => P.h * E t * z.I t) volume 0 P.T :=
        ((continuousOn_const.mul hEc.continuousOn).mul hIc).intervalIntegrable
      exact (h1.sub h2).congr (fun t _ => by ring)
  have hQyint : ∫ t in (0:ℝ)..P.T, ((φ t - P.c * E t) * y.p t + (ψ t - P.h * E t) * y.I t) ≤ 0 := by
    have := intervalIntegral.integral_mono_on hT.le (hQint y hya) intervalIntegrable_const
      (fun t ht => hQ y hya t ht)
    simpa using this
  have hQxint : ∫ t in (0:ℝ)..P.T, ((φ t - P.c * E t) * x.p t + (ψ t - P.h * E t) * x.I t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => by
      rw [uIcc_of_le hT.le] at ht; exact hQx t ht)]
    simp
  have hysi : IntervalIntegrable y.s volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hya.2.1
  have hxsi : IntervalIntegrable x.s volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hxa.2.1
  have hW := weighted_le hT.le hysi hxsi hg'i hg'neg hgT (hcmp y hya)
  have hA : ∫ t in (0:ℝ)..P.T, (P.price * E t - φ t) * y.s t ≤
      ∫ t in (0:ℝ)..P.T, (P.price * E t - φ t) * x.s t := by
    simp_rw [hgform]; exact hW
  have hyIT : 0 ≤ y.I P.T := hya.2.2.2.2.2.2.2
  have hprod : 0 ≤ φ P.T * y.I P.T := mul_nonneg hφT hyIT
  simp only [hφ, hE] at hA hQyint hQxint hprod
  rw [idy, idx, hxIT]
  linarith

lemma lin_nonneg {S d : ℝ → ℝ} {w T : ℝ} (hT : 0 ≤ T) (hS : ContinuousOn S (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T)) (hd0 : ∀ t ∈ Icc 0 T, 0 ≤ d t)
    (hform : ∀ t ∈ Icc 0 T, S t = 0 + ∫ u in (0:ℝ)..t, (d u - w * S u)) :
    ∀ t ∈ Icc 0 T, 0 ≤ S t := by
  have dS := hasDerivWithinAt_of_integral (F := S) hT (hd.sub (continuousOn_const.mul hS)) hform
  have hS0 : S 0 = 0 := by rw [hform 0 ⟨le_refl _, hT⟩]; simp
  have key := nonpos_of_deriv_le_pos_part (η := fun t => -(Real.exp (w * t) * S t))
    (η' := fun t => -(Real.exp (w * t) * d t)) (K := 0) (a := 0) (b := T) (le_refl _)
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hS).neg)
    (by
      intro t ht
      have h1 : HasDerivWithinAt (fun t => Real.exp (w * t)) (Real.exp (w * t) * (w * 1))
          (Ici t) t := (((hasDerivAt_id t).const_mul w).exp).hasDerivWithinAt
      have h2 := (h1.mul (dS t ht)).neg
      apply h2.congr_deriv
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring)
    (by simp [hS0])
    (by
      intro t ht
      have := hd0 t ⟨ht.1, ht.2.le⟩
      have := Real.exp_pos (w * t)
      simp only [zero_mul]
      nlinarith)
  intro t ht
  have := key t ht
  have hpos := Real.exp_pos (w * t)
  by_contra hc
  rw [not_le] at hc
  have := mul_neg_of_pos_of_neg hpos hc
  linarith

lemma lin_formula {I d : ℝ → ℝ} {r T I0 : ℝ} (hT : 0 ≤ T) (hI : ContinuousOn I (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hform : ∀ t ∈ Icc 0 T, I t = I0 + ∫ u in (0:ℝ)..t, (r * I u - d u)) :
    ∀ t ∈ Icc 0 T, Real.exp (-(r * t)) * I t = I0 - ∫ u in (0:ℝ)..t, Real.exp (-(r * u)) * d u := by
  have dI := hasDerivWithinAt_of_integral (F := I) hT
    ((continuousOn_const.mul hI).sub hd) hform
  have hed : ContinuousOn (fun u => Real.exp (-(r * u)) * d u) (Icc 0 T) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(r * u))).continuousOn.mul hd
  have hGi : ∀ t ∈ Icc 0 T, (fun t => ∫ u in (0:ℝ)..t, Real.exp (-(r * u)) * d u) t =
      0 + ∫ u in (0:ℝ)..t, Real.exp (-(r * u)) * d u := fun t _ => by simp
  have dG := hasDerivWithinAt_of_integral hT hed hGi
  have cG := continuousOn_of_integral hT hed hGi
  have hc := constant_of_has_deriv_right_zero
    (f := fun t => Real.exp (-(r * t)) * I t + ∫ u in (0:ℝ)..t, Real.exp (-(r * u)) * d u)
    (((by fun_prop : Continuous fun u : ℝ => Real.exp (-(r * u))).continuousOn.mul hI).add cG)
    (by
      intro t ht
      have h0 : HasDerivAt (fun u => -(r * u)) (-r) t :=
        (((hasDerivAt_id' t).const_mul r).neg).congr_deriv (by ring)
      have h1 := (h0.exp.hasDerivWithinAt (s := Ici t)).mul (dI t ht)
      have h2 := h1.add (dG t ht)
      apply h2.congr_deriv
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring)
  intro t ht
  have := hc t ht
  have hI0 : I 0 = I0 := by rw [hform 0 ⟨le_refl _, hT⟩]; simp
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, intervalIntegral.integral_same,
    add_zero, hI0] at this
  linarith

end SRLib

open SRLib in
theorem solution (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ) (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    Ilow < P.IL → P.IL < Ihigh → ∃ tp ∈ Set.Icc 0 P.T, ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdOnFrom P x tp ∧ DepletedExactlyAtT P x := by
  intro hlo hhi
  have hT : 0 < P.T := hP.2.2.2.2.2.2.1
  have hr : 0 < P.r := by linarith [hP.2.2.1, hP.2.2.2.1]
  have hm : 0 < P.m := hP.2.2.2.2.2.1
  have hα : 0 < P.alpha := hP.2.2.2.2.2.2.2.1
  have hβ : 0 ≤ P.beta := hP.2.2.2.2.2.2.2.2.1
  have hTm : P.T ∈ Icc 0 P.T := ⟨hT.le, le_refl _⟩
  have h0m : (0:ℝ) ∈ Icc 0 P.T := ⟨le_refl _, hT.le⟩
  obtain ⟨x0, hx0a, hx0p, hx0s, hx0IT, -⟩ := hhigh
  obtain ⟨x1, hx1a, hx1p, hx1s, hx1IT, -⟩ := hlow
  have f0 := salesOn_form P Ihigh x0 hx0a hx0s
  have f1 := salesOn_form P Ilow x1 hx1a hx1s
  obtain ⟨-, -, hD, hS, -, hode0, hcon0, -⟩ := hx0a
  obtain ⟨-, -, hD1, hS1, hI1, hode1, -, -⟩ := hx1a
  have huniq := salesOn_unique P hT.le x1 x0 hD1 hS1 hD hS f1 f0
  set d := x0.d P with hddef
  have hd : ContinuousOn d (Icc 0 P.T) := d_continuousOn P x0 hD hS
  have hDi : ∀ t ∈ Icc 0 P.T, x0.D t = ∫ u in (0:ℝ)..t, d u :=
    fun t ht => (f0 t ht).1.trans (zero_add _)
  have hd0 : ∀ t ∈ Icc 0 P.T, 0 ≤ d t := by
    intro t ht
    have := (hcon0 t ht).2.2.1
    rw [hx0s t ht] at this
    exact this
  -- positivity of demand
  have hSnn : ∀ t ∈ Icc 0 P.T, 0 ≤ x0.S t := lin_nonneg hT.le hS hd hd0 (fun t ht => (f0 t ht).2)
  have hRem := remaining_formula P hm.ne' hT.le x0 hD hS hDi
  have hdpos : ∀ t ∈ Icc 0 P.T, 0 < d t := by
    intro t ht
    have h1 : 0 < P.m - x0.D t := by rw [hRem t ht]; positivity
    have h2 : 0 < P.alpha + P.beta * x0.S t / P.m := by
      have := hSnn t ht; positivity
    show 0 < (P.alpha + P.beta * x0.S t / P.m) * (P.m - x0.D t)
    exact mul_pos h2 h1
  -- D(T) = Ihigh
  have hDT : x0.D P.T = Ihigh := by
    have h1 := (hode0 P.T hTm).2.2
    have h2 : ∫ u in (0:ℝ)..P.T, (x0.p u - x0.s u) = ∫ u in (0:ℝ)..P.T, (-(d u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hT.le] at hu
      simp only
      rw [hx0p u hu, hx0s u hu]
      simp [withIL_d, hddef]
    rw [h2, intervalIntegral.integral_neg, ← hDi P.T hTm] at h1
    change x0.I P.T = 0 at hx0IT
    change x0.I P.T = Ihigh + -x0.D P.T at h1
    linarith
  -- G and Ilow = G T
  set G : ℝ → ℝ := fun t => ∫ u in (0:ℝ)..t, Real.exp (-(P.r * u)) * d u with hG
  have hed : ContinuousOn (fun u => Real.exp (-(P.r * u)) * d u) (Icc 0 P.T) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-(P.r * u))).continuousOn.mul hd
  have hGi : ∀ t ∈ Icc 0 P.T, G t = 0 + ∫ u in (0:ℝ)..t, Real.exp (-(P.r * u)) * d u :=
    fun t _ => by simp [hG]
  have dG := hasDerivWithinAt_of_integral hT.le hed hGi
  have cG := continuousOn_of_integral hT.le hed hGi
  have hGT : G P.T = Ilow := by
    have hform1 : ∀ t ∈ Icc 0 P.T, x1.I t = Ilow + ∫ u in (0:ℝ)..t, (P.r * x1.I u - d u) := by
      intro t ht
      rw [(hode1 t ht).2.2]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      have hu' : u ∈ Icc 0 P.T := ⟨hu.1, hu.2.trans ht.2⟩
      simp only
      rw [hx1p u hu', hx1s u hu']
      have h1 := huniq u hu'
      show P.r * x1.I u - x1.d P u = P.r * x1.I u - x0.d P u
      simp only [Traj.d, h1.1, h1.2]
    have := lin_formula hT.le hI1 hd hform1 P.T hTm
    change x1.I P.T = 0 at hx1IT
    rw [hx1IT, mul_zero] at this
    simp only [hG]; linarith
  -- the switching function
  set Φ : ℝ → ℝ := fun τ => (P.IL - x0.D τ) * Real.exp (-(P.r * τ)) - (G P.T - G τ) with hΦ
  have cΦ : ContinuousOn Φ (Icc 0 P.T) :=
    ((continuousOn_const.sub hD).mul
      (by fun_prop : Continuous fun u : ℝ => Real.exp (-(P.r * u))).continuousOn).sub
      (continuousOn_const.sub cG)
  have hD0 : x0.D 0 = 0 := by rw [hDi 0 h0m]; simp
  have hΦ0 : Φ 0 = P.IL - Ilow := by simp [hΦ, hD0, hG, ← hGT]
  have hΦT : Φ P.T < 0 := by
    simp only [hΦ, hDT, sub_self, sub_zero]
    exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
  obtain ⟨tp, htp, hΦtp⟩ : ∃ tp ∈ Icc 0 P.T, Φ tp = 0 := by
    have := intermediate_value_Icc' hT.le cΦ
    exact this ⟨hΦT.le, by rw [hΦ0]; linarith⟩
  have htpT : tp < P.T := by
    rcases lt_or_eq_of_le htp.2 with h | h
    · exact h
    · rw [h] at hΦtp; linarith
  have hkey : (P.IL - x0.D tp) * Real.exp (-(P.r * tp)) = G P.T - G tp := by
    have := hΦtp; simp only [hΦ] at this; linarith
  -- the inventory path
  set I : ℝ → ℝ := fun t => Real.exp (P.r * max t tp) *
    ((P.IL - x0.D (min t tp)) * Real.exp (-(P.r * tp)) - (G (max t tp) - G tp)) with hIdef
  have I_ge : ∀ v, tp ≤ v → I v = Real.exp (P.r * v) * (G P.T - G v) := by
    intro v hv
    simp only [hIdef, max_eq_left hv, min_eq_right hv, hkey]
    ring
  have I_le : ∀ v, v ≤ tp → I v = P.IL - x0.D v := by
    intro v hv
    simp only [hIdef, max_eq_right hv, min_eq_left hv, sub_self, sub_zero]
    rw [mul_comm, mul_assoc, ← Real.exp_add]
    simp
  have hGdiff : ∀ t ∈ Icc 0 P.T, G P.T - G t = ∫ u in t..P.T, Real.exp (-(P.r * u)) * d u := by
    intro t ht
    simp only [hG]
    exact intervalIntegral.integral_interval_sub_left (hed.intervalIntegrable_of_Icc hT.le)
      (ii_of_cont hed ht)
  have hGpos : ∀ t ∈ Icc 0 P.T, t < P.T → 0 < G P.T - G t := by
    intro t ht htT
    rw [hGdiff t ht]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact (hed.mono (Icc_subset_Icc ht.1 le_rfl)).intervalIntegrable_of_Icc htT.le
    · intro u hu
      exact mul_pos (Real.exp_pos _) (hdpos u ⟨ht.1.trans hu.1.le, hu.2.le⟩)
    · exact htT
  have htpI : tp ∈ Icc 0 P.T := htp
  have hDmono : ∀ t ∈ Icc 0 P.T, t ≤ tp → x0.D t ≤ x0.D tp := by
    intro t ht htt
    rw [hDi t ht, hDi tp htp]
    have := intervalIntegral.integral_interval_sub_left (ii_of_cont hd htp) (ii_of_cont hd ht)
    have h2 : 0 ≤ ∫ u in t..tp, d u := intervalIntegral.integral_nonneg htt
      (fun u hu => hd0 u ⟨ht.1.trans hu.1, hu.2.trans htp.2⟩)
    linarith
  have I_pos : ∀ t ∈ Ico 0 P.T, 0 < I t := by
    intro t ht
    by_cases h : tp ≤ t
    · rw [I_ge t h]; exact mul_pos (Real.exp_pos _) (hGpos t ⟨ht.1, ht.2.le⟩ ht.2)
    · rw [not_le] at h
      rw [I_le t h.le]
      have h1 := hDmono t ⟨ht.1, ht.2.le⟩ h.le
      have h2 : 0 < P.IL - x0.D tp := by
        rw [← I_le tp le_rfl, I_ge tp le_rfl]
        exact mul_pos (Real.exp_pos _) (hGpos tp htp htpT)
      linarith
  have I_T : I P.T = 0 := by rw [I_ge P.T htp.2]; simp
  have I_nn : ∀ t ∈ Icc 0 P.T, 0 ≤ I t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact (I_pos t ⟨ht.1, h⟩).le
    · rw [h, I_T]
  have cI : ContinuousOn I (Icc 0 P.T) := by
    have hmax : MapsTo (fun t => max t tp) (Icc 0 P.T) (Icc 0 P.T) :=
      fun t ht => ⟨le_max_of_le_left ht.1, max_le ht.2 htp.2⟩
    have hmin : MapsTo (fun t => min t tp) (Icc 0 P.T) (Icc 0 P.T) :=
      fun t ht => ⟨le_min ht.1 htp.1, (min_le_left _ _).trans ht.2⟩
    have c1 : ContinuousOn (fun t => G (max t tp)) (Icc 0 P.T) :=
      cG.comp (continuous_id.max continuous_const).continuousOn hmax
    have c2 : ContinuousOn (fun t => x0.D (min t tp)) (Icc 0 P.T) :=
      hD.comp (continuous_id.min continuous_const).continuousOn hmin
    have c3 : Continuous (fun t => Real.exp (P.r * max t tp)) := by fun_prop
    exact c3.continuousOn.mul (((continuousOn_const.sub c2).mul continuousOn_const).sub
      (c1.sub continuousOn_const))
  set pp : ℝ → ℝ := fun t => if t < tp then 0 else P.r * I t with hpp
  have hpp_ind : pp = (Ici tp).indicator (fun t => P.r * I t) := by
    funext t
    by_cases h : t < tp
    · have : t ∉ Ici tp := fun h' => (not_le.mpr h) h'
      simp [hpp, h, this]
    · have : t ∈ Ici tp := not_lt.mp h
      simp [hpp, h, this]
  have hppi : IntegrableOn pp (Icc 0 P.T) := by
    rw [hpp_ind]
    exact ((continuousOn_const.mul cI).integrableOn_Icc).indicator measurableSet_Ici
  have hppii : IntervalIntegrable pp volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hppi
  have hdii : IntervalIntegrable d volume 0 P.T := hd.intervalIntegrable_of_Icc hT.le
  -- inventory equation
  have hbefore : ∀ t ∈ Icc 0 P.T, t ≤ tp → ∫ u in (0:ℝ)..t, (pp u - d u) = -x0.D t := by
    intro t ht htt
    rw [hDi t ht, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton tp)] with u hu hmem
    rw [uIoc_of_le ht.1] at hmem
    have hlt : u < tp := lt_of_le_of_ne (hmem.2.trans htt) hu
    simp [hpp, hlt]
  have hIode : ∀ t ∈ Icc 0 P.T, I t = P.IL + ∫ u in (0:ℝ)..t, (pp u - d u) := by
    intro t ht
    by_cases htt : t ≤ tp
    · rw [hbefore t ht htt, I_le t htt]; ring
    · rw [not_le] at htt
      have hsub : IntervalIntegrable (fun u => pp u - d u) volume 0 P.T := hppii.sub hdii
      have hi1 : IntervalIntegrable (fun u => pp u - d u) volume 0 tp :=
        hsub.mono_set (by rw [uIcc_of_le htp.1, uIcc_of_le hT.le]; exact Icc_subset_Icc le_rfl htp.2)
      have hi2 : IntervalIntegrable (fun u => pp u - d u) volume tp t :=
        hsub.mono_set (by rw [uIcc_of_le htt.le, uIcc_of_le hT.le]; exact Icc_subset_Icc htp.1 ht.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hbefore tp htp le_rfl]
      have hcongr : ∫ u in tp..t, (pp u - d u) = ∫ u in tp..t, (P.r * I u - d u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le htt.le] at hu
        simp [hpp, not_lt.mpr hu.1]
      have hftc : ∫ u in tp..t, (P.r * I u - d u) = I t - I tp := by
        apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le htt.le
        · exact cI.mono (Icc_subset_Icc htp.1 ht.2)
        · intro u hu
          have hu0 : u ∈ Ico 0 P.T := ⟨htp.1.trans hu.1.le, hu.2.trans_le ht.2⟩
          have h1 : HasDerivWithinAt (fun v => Real.exp (P.r * v) * (G P.T - G v))
              (Real.exp (P.r * u) * P.r * (G P.T - G u) +
                Real.exp (P.r * u) * (-(Real.exp (-(P.r * u)) * d u))) (Ici u) u := by
            have e1 : HasDerivAt (fun v => Real.exp (P.r * v)) (Real.exp (P.r * u) * P.r) u := by
              have := ((hasDerivAt_id' u).const_mul P.r).exp
              exact this.congr_deriv (by ring)
            exact e1.hasDerivWithinAt.mul ((dG u hu0).const_sub (G P.T))
          have h2 : HasDerivWithinAt I _ (Ioi u) u := (h1.mono (Ioi_subset_Ici_self)).congr_of_eventuallyEq
            (by
              filter_upwards [self_mem_nhdsWithin] with v hv
              exact I_ge v (hu.1.trans hv).le) (I_ge u hu.1.le)
          apply h2.congr_deriv
          rw [I_ge u hu.1.le]
          have : Real.exp (P.r * u) * Real.exp (-(P.r * u)) = 1 := by
            rw [← Real.exp_add]; simp
          linear_combination (-(d u)) * this
        · exact (((continuousOn_const.mul cI).sub hd).mono
            (Icc_subset_Icc htp.1 ht.2)).intervalIntegrable_of_Icc htt.le
      rw [hcongr, hftc, I_le tp le_rfl]; ring
  set x : Traj := Traj.mk x0.D x0.S I pp d with hxdef
  have hxa : IsAdmissible P x := by
    refine ⟨hppi, hd.integrableOn_Icc, hD, hS, cI, ?_, ?_, ?_⟩
    · intro t ht
      exact ⟨hDi t ht, (f0 t ht).2.trans (zero_add _), hIode t ht⟩
    · intro t ht
      have hI0 := I_nn t ht
      refine ⟨?_, ?_, hd0 t ht, le_refl _⟩
      · show 0 ≤ pp t
        simp only [hpp]; split_ifs
        · exact le_refl _
        · exact mul_nonneg hr.le hI0
      · show pp t ≤ P.r * I t
        simp only [hpp]; split_ifs
        · exact mul_nonneg hr.le hI0
        · exact le_refl _
    · show 0 ≤ I P.T
      rw [I_T]
  have hxp : ProdOnFrom P x tp := fun t _ => rfl
  have hcmp : ∀ y : Traj, IsAdmissible P y → ∀ t ∈ Icc 0 P.T,
      ∫ u in (0:ℝ)..t, y.s u ≤ ∫ u in (0:ℝ)..t, x.s u := by
    intro y hya t ht
    obtain ⟨-, hysi, hyD, hyS, -, hyode, hycon, -⟩ := hya
    have hyd := d_continuousOn P y hyD hyS
    have hc := demand_le P hP x0 y hD hS
      (fun t ht => ⟨hDi t ht, (f0 t ht).2.trans (zero_add _)⟩)
      hyD hyS hysi (fun t ht => ⟨(hyode t ht).1, (hyode t ht).2.1⟩)
      (fun t ht => (hycon t ht).2.2.2) t ht
    have h1 : ∫ u in (0:ℝ)..t, y.s u ≤ ∫ u in (0:ℝ)..t, y.d P u :=
      intervalIntegral.integral_mono_on ht.1 (ii_of_int hysi ht) (ii_of_cont hyd ht)
        (fun u hu => (hycon u ⟨hu.1, hu.2.trans ht.2⟩).2.2.2)
    have h2 := (hyode t ht).1
    have h3 := hDi t ht
    show ∫ u in (0:ℝ)..t, y.s u ≤ ∫ u in (0:ℝ)..t, d u
    linarith
  refine ⟨tp, htp, x, ⟨hxa, b_optimal P hP hSR x hxa tp htp hxp I_T hcmp⟩, fun t _ => rfl, hxp,
    I_T, I_pos⟩
