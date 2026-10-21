-- Prove2me | solution 1 for SelfReplic.Strong.theorem_1_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:25:27.835632+00:00
-- url     : https://prove2.me/submissions/b8c22dcb-e4c0-49fc-96f8-9ecb11d31b82

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

end SRLib


open MeasureTheory Set SelfReplic.Strong Filter Topology

namespace SRLib

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

/-- Discounted revenue is monotone in the cumulative-sales path. -/
lemma discounted_le (ρ T : ℝ) (hρ : 0 ≤ ρ) (hT : 0 ≤ T) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) (hg : IntervalIntegrable g volume 0 T)
    (hle : ∀ t ∈ Icc 0 T, ∫ u in (0:ℝ)..t, f u ≤ ∫ u in (0:ℝ)..t, g u) :
    ∫ t in (0:ℝ)..T, f t * Real.exp (-(ρ * t)) ≤ ∫ t in (0:ℝ)..T, g t * Real.exp (-(ρ * t)) := by
  have hE : IntervalIntegrable (fun u => -ρ * Real.exp (-(ρ * u))) volume 0 T :=
    (by fun_prop : Continuous fun u => -ρ * Real.exp (-(ρ * u))).intervalIntegrable _ _
  have key : ∀ k : ℝ → ℝ, IntervalIntegrable k volume 0 T →
      ∫ t in (0:ℝ)..T, k t * Real.exp (-(ρ * t)) =
        Real.exp (-(ρ * T)) * (∫ u in (0:ℝ)..T, k u) +
          ρ * ∫ t in (0:ℝ)..T, Real.exp (-(ρ * t)) * ∫ u in (0:ℝ)..t, k u := by
    intro k hk
    have := bp2 (G0 := 1) hk hE
    simp_rw [← exp_form] at this
    rw [show (fun t => k t * Real.exp (-(ρ * t))) = fun t => Real.exp (-(ρ * t)) * k t from
      funext fun t => mul_comm _ _, this]
    rw [show (fun t => -ρ * Real.exp (-(ρ * t)) * ∫ u in (0:ℝ)..t, k u) =
      fun t => -ρ * (Real.exp (-(ρ * t)) * ∫ u in (0:ℝ)..t, k u) from
      funext fun t => by ring, intervalIntegral.integral_const_mul]
    ring
  rw [key f hf, key g hg]
  have hcf : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, f u) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
      (μ := volume) (f := f) (by rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hf)
    rwa [uIcc_of_le hT] at this
  have hcg : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, g u) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
      (μ := volume) (f := g) (by rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hg)
    rwa [uIcc_of_le hT] at this
  have hexpc : Continuous fun t : ℝ => Real.exp (-(ρ * t)) := by fun_prop
  have hmono : ∫ t in (0:ℝ)..T, Real.exp (-(ρ * t)) * ∫ u in (0:ℝ)..t, f u ≤
      ∫ t in (0:ℝ)..T, Real.exp (-(ρ * t)) * ∫ u in (0:ℝ)..t, g u := by
    apply intervalIntegral.integral_mono_on hT
    · exact (hexpc.continuousOn.mul hcf).intervalIntegrable_of_Icc hT
    · exact (hexpc.continuousOn.mul hcg).intervalIntegrable_of_Icc hT
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hle t ht) (Real.exp_pos _).le
  have h1 := hle T ⟨hT, le_refl _⟩
  have h2 := Real.exp_pos (-(ρ * T))
  nlinarith

end SRLib

open SRLib in
theorem solution (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ) (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    Ihigh < P.IL → ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdAlwaysOff P x ∧ 0 < x.I P.T := by
  intro hIL
  have hT : 0 < P.T := hP.2.2.2.2.2.2.1
  have hr : 0 < P.r := by linarith [hP.2.2.1, hP.2.2.2.1]
  have hρ : 0 ≤ P.rho := hP.2.2.2.1
  have hc : 0 ≤ P.c := hP.2.2.2.2.2.2.2.2.2.1
  have hh : 0 ≤ P.h := hP.2.2.2.2.2.2.2.2.2.2
  have hπ : 0 ≤ P.price := by linarith [hP.2.1]
  have hTm : P.T ∈ Icc 0 P.T := ⟨hT.le, le_refl _⟩
  obtain ⟨x0, hx0a, hx0p, hx0s, hx0IT, -⟩ := hhigh
  have f0 := salesOn_form P Ihigh x0 hx0a hx0s
  obtain ⟨-, -, hD, hS, -, hode0, hcon0, -⟩ := hx0a
  have hd := d_continuousOn P x0 hD hS
  -- inventory of x0 is `Ihigh - D`, hence `D ≤ Ihigh`
  have hDle : ∀ t ∈ Icc 0 P.T, x0.D t ≤ Ihigh := by
    intro t ht
    have h1 := (hode0 t ht).2.2
    have h2 : ∫ u in (0:ℝ)..t, (x0.p u - x0.s u) = ∫ u in (0:ℝ)..t, (-(x0.d P u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ht.1] at hu
      have hu' : u ∈ Icc 0 P.T := ⟨hu.1, hu.2.trans ht.2⟩
      simp only
      rw [hx0p u hu', hx0s u hu']
      simp [withIL_d]
    rw [h2, intervalIntegral.integral_neg, ← (f0 t ht).1.trans (zero_add _)] at h1
    have h3 := (hcon0 t ht)
    have h4 : 0 ≤ P.r * x0.I t := h3.1.trans h3.2.1
    have h5 : 0 ≤ x0.I t := (mul_nonneg_iff_of_pos_left hr).mp h4
    change x0.I t = Ihigh + -x0.D t at h1
    linarith
  have hd0 : ∀ t ∈ Icc 0 P.T, 0 ≤ x0.d P t := by
    intro t ht
    have := (hcon0 t ht).2.2.1
    rw [hx0s t ht] at this
    exact this
  set x : Traj := Traj.mk x0.D x0.S (fun t => P.IL - x0.D t) (fun _ => 0) (x0.d P) with hxdef
  have hxd : x.d P = x0.d P := rfl
  have hDi : ∀ t ∈ Icc 0 P.T, x0.D t = ∫ u in (0:ℝ)..t, x0.d P u :=
    fun t ht => (f0 t ht).1.trans (zero_add _)
  have hxa : IsAdmissible P x := by
    refine ⟨integrableOn_const (by simp), hd.integrableOn_Icc, hD, hS,
      continuousOn_const.sub hD, ?_, ?_, ?_⟩
    · intro t ht
      refine ⟨hDi t ht, (f0 t ht).2.trans (zero_add _), ?_⟩
      show P.IL - x0.D t = P.IL + ∫ u in (0:ℝ)..t, (0 - x0.d P u)
      rw [intervalIntegral.integral_sub intervalIntegrable_const (ii_of_cont hd ht), hDi t ht]
      simp; ring
    · intro t ht
      refine ⟨le_refl _, ?_, hd0 t ht, le_refl _⟩
      show (0:ℝ) ≤ P.r * (P.IL - x0.D t)
      have := hDle t ht
      nlinarith
    · show (0:ℝ) ≤ P.IL - x0.D P.T
      linarith [hDle P.T hTm]
  refine ⟨x, ⟨hxa, ?_⟩, fun t _ => rfl, fun t _ => rfl, ?_⟩
  swap
  · show (0:ℝ) < P.IL - x0.D P.T
    linarith [hDle P.T hTm]
  intro y hya
  obtain ⟨hypi, hysi, hyD, hyS, hyI, hyode, hycon, hyIT⟩ := hya
  set E : ℝ → ℝ := fun t => Real.exp (-(P.rho * t)) with hE
  have hEc : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hypii : IntervalIntegrable y.p volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hypi
  have hysii : IntervalIntegrable y.s volume 0 P.T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hysi
  have hyIi : IntervalIntegrable y.I volume 0 P.T := hyI.intervalIntegrable_of_Icc hT.le
  have hdii : IntervalIntegrable (x0.d P) volume 0 P.T := hd.intervalIntegrable_of_Icc hT.le
  -- comparison of cumulative sales
  have hyd := d_continuousOn P y hyD hyS
  have hcmp := demand_le P hP x0 y hD hS (fun t ht => ⟨hDi t ht, (f0 t ht).2.trans (zero_add _)⟩)
    hyD hyS hysi (fun t ht => ⟨(hyode t ht).1, (hyode t ht).2.1⟩)
    (fun t ht => (hycon t ht).2.2.2)
  have hSig : ∀ t ∈ Icc 0 P.T, ∫ u in (0:ℝ)..t, y.s u ≤ ∫ u in (0:ℝ)..t, x0.d P u := by
    intro t ht
    have h1 : ∫ u in (0:ℝ)..t, y.s u ≤ ∫ u in (0:ℝ)..t, y.d P u :=
      intervalIntegral.integral_mono_on ht.1 (ii_of_int hysi ht) (ii_of_cont hyd ht)
        (fun u hu => (hycon u ⟨hu.1, hu.2.trans ht.2⟩).2.2.2)
    rw [← (hyode t ht).1, ← hDi t ht] at *
    linarith [hcmp t ht]
  have hrev := discounted_le P.rho P.T hρ hT.le hysii hdii hSig
  -- inventory comparison
  have hIy : ∀ t ∈ Icc 0 P.T, P.IL - x0.D t ≤ y.I t := by
    intro t ht
    rw [(hyode t ht).2.2, intervalIntegral.integral_sub (ii_of_int hypi ht) (ii_of_int hysi ht)]
    have hp0 : 0 ≤ ∫ u in (0:ℝ)..t, y.p u :=
      intervalIntegral.integral_nonneg ht.1 (fun u hu => (hycon u ⟨hu.1, hu.2.trans ht.2⟩).1)
    have := hSig t ht
    rw [← hDi t ht] at this
    linarith
  -- split profits
  have hsplit : ∀ z : Traj, IntervalIntegrable z.s volume 0 P.T →
      IntervalIntegrable z.p volume 0 P.T → IntervalIntegrable z.I volume 0 P.T →
      profit P z = P.price * (∫ t in (0:ℝ)..P.T, z.s t * E t) -
        ∫ t in (0:ℝ)..P.T, (P.c * z.p t + P.h * z.I t) * E t := by
    intro z hs hp hI
    unfold profit
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · congr 1; ext t; simp only [hE]; ring
    · exact (hs.mul_continuousOn hEc.continuousOn).const_mul _
    · exact ((hp.const_mul _).add (hI.const_mul _)).mul_continuousOn hEc.continuousOn
  have hxI : IntervalIntegrable x.I volume 0 P.T :=
    (continuousOn_const.sub hD).intervalIntegrable_of_Icc hT.le
  rw [hsplit y hysii hypii hyIi, hsplit x hdii intervalIntegrable_const hxI]
  have hcost : ∫ t in (0:ℝ)..P.T, (P.c * x.p t + P.h * x.I t) * E t ≤
      ∫ t in (0:ℝ)..P.T, (P.c * y.p t + P.h * y.I t) * E t := by
    apply intervalIntegral.integral_mono_on hT.le
    · exact ((intervalIntegrable_const.const_mul _).add (hxI.const_mul _)).mul_continuousOn
        hEc.continuousOn
    · exact ((hypii.const_mul _).add (hyIi.const_mul _)).mul_continuousOn hEc.continuousOn
    · intro t ht
      have h1 := hIy t ht
      have h2 := (hycon t ht).1
      have h3 := hEpos t
      show (P.c * 0 + P.h * (P.IL - x0.D t)) * E t ≤ (P.c * y.p t + P.h * y.I t) * E t
      apply mul_le_mul_of_nonneg_right _ h3.le
      nlinarith
  have hrev' : ∫ t in (0:ℝ)..P.T, y.s t * E t ≤ ∫ t in (0:ℝ)..P.T, x.s t * E t := hrev
  nlinarith
