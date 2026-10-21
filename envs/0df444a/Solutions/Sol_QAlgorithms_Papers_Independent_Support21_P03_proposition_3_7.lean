-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:04:50.763406+00:00
-- url     : https://prove2.me/submissions/3e221ee4-6e31-4ccd-9c82-aeae0b2c6c74

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

theorem g66f_flow_comp (D : NonsingularSystem K M) (t s : K.Carrier) :
    (D.flow (t + s) : M → M) = D.flow t ∘ D.flow s := by
  funext x; exact D.flow_add t s x

theorem g66f_push_add (D : NonsingularSystem K M) (t s : K.Carrier) :
    pushedReference D (t + s) = (pushedReference D s).map (D.flow t) := by
  unfold pushedReference
  rw [Measure.map_map (D.flow t).measurable (D.flow s).measurable, g66f_flow_comp]

instance g66f_push_fin (D : NonsingularSystem K M) (t : K.Carrier) :
    IsFiniteMeasure (pushedReference D t) := by
  unfold pushedReference; infer_instance

/-- transfer an a.e. property along the flow -/
theorem g66f_transfer (D : NonsingularSystem K M) (u : K.Carrier) {P : M → Prop}
    (h : ∀ᵐ z ∂(D.omega : Measure M), P z) : ∀ᵐ x ∂(D.omega : Measure M), P (D.flow u x) := by
  have h2 : ∀ᵐ z ∂(pushedReference D u), P z := (D.equivalent u).1 h
  exact ae_of_ae_map (D.flow u).measurable.aemeasurable h2

theorem g66f_pos (D : NonsingularSystem K M) (t : K.Carrier) :
    ∀ᵐ z ∂(D.omega : Measure M), 0 < (pushedReference D t).rnDeriv (D.omega : Measure M) z ∧
      (pushedReference D t).rnDeriv (D.omega : Measure M) z < ∞ := by
  have h1 := Measure.rnDeriv_pos (D.equivalent t).1
  have h1' : ∀ᵐ z ∂(D.omega : Measure M),
      0 < (pushedReference D t).rnDeriv (D.omega : Measure M) z := (D.equivalent t).2 h1
  filter_upwards [h1', Measure.rnDeriv_lt_top (pushedReference D t) (D.omega : Measure M)]
    with z hz1 hz2 using ⟨hz1, hz2⟩

theorem g66f_chain (D : NonsingularSystem K M) (t s : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M),
      (pushedReference D (t + s)).rnDeriv (D.omega : Measure M) (D.flow (t + s) x) =
        (pushedReference D s).rnDeriv (D.omega : Measure M) (D.flow s x) *
          (pushedReference D t).rnDeriv (D.omega : Measure M) (D.flow (t + s) x) := by
  set ω := (D.omega : Measure M)
  have hac : pushedReference D (t + s) ≪ pushedReference D t := by
    rw [g66f_push_add]; exact (D.equivalent s).1.map (D.flow t).measurable
  have hB := Measure.rnDeriv_mul_rnDeriv (κ := ω) hac
  have hC := (D.flow t).measurableEmbedding.rnDeriv_map (pushedReference D s) ω
  have hB' := g66f_transfer D (t + s) hB
  have hC' := g66f_transfer D s hC
  filter_upwards [hB', hC'] with x hx1 hx2
  rw [← hx1, Pi.mul_apply]
  congr 1
  rw [← hx2]
  rw [g66f_push_add]
  show _ = (Measure.map (⇑(D.flow t)) (pushedReference D s)).rnDeriv (pushedReference D t)
    (D.flow t (D.flow s x))
  rw [← D.flow_add]

theorem g66f_cocycle (D : NonsingularSystem K M) (t s : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D (t + s) x = entropyCocycle D s x + entropyCocycle D t (D.flow s x) := by
  filter_upwards [g66f_chain D t s, g66f_transfer D s (g66f_pos D s),
    g66f_transfer D (t + s) (g66f_pos D t)] with x h1 h2 h3
  unfold entropyCocycle logDensity referenceRNReal
  rw [← D.flow_add, h1, ENNReal.toReal_mul]
  rw [Real.log_mul (ENNReal.toReal_pos h2.1.ne' h2.2.ne).ne'
    (ENNReal.toReal_pos h3.1.ne' h3.2.ne).ne']

theorem g66f_zero (D : NonsingularSystem K M) :
    ∀ᵐ x ∂(D.omega : Measure M), entropyCocycle D 0 x = 0 := by
  have hid : pushedReference D 0 = (D.omega : Measure M) := by
    unfold pushedReference
    have : (D.flow 0 : M → M) = id := funext D.flow_zero
    rw [this, Measure.map_id]
  have h := Measure.rnDeriv_self (D.omega : Measure M)
  filter_upwards [h] with x hx
  unfold entropyCocycle logDensity referenceRNReal
  rw [D.flow_zero, hid, hx]; simp

theorem g66f_inv (D : NonsingularSystem K M) (t : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M), entropyCocycle D (-t) x = -entropyCocycle D t (D.flow (-t) x) := by
  filter_upwards [g66f_cocycle D t (-t), g66f_zero D] with x h1 h2
  rw [add_neg_cancel, h2] at h1
  linarith

theorem g66f_log_meas (D : NonsingularSystem K M) (t : K.Carrier) : Measurable (logDensity D t) := by
  unfold logDensity referenceRNReal
  exact (Measure.measurable_rnDeriv _ _).ennreal_toReal.log

theorem g66f_exp_log (D : NonsingularSystem K M) (t : K.Carrier) :
    ∀ᵐ z ∂(D.omega : Measure M), (pushedReference D t).rnDeriv (D.omega : Measure M) z =
      ENNReal.ofReal (Real.exp (logDensity D t z)) := by
  filter_upwards [g66f_pos D t] with z hz
  unfold logDensity referenceRNReal
  rw [Real.exp_log (ENNReal.toReal_pos hz.1.ne' hz.2.ne), ENNReal.ofReal_toReal hz.2.ne]

theorem g66f_es_sym (D : NonsingularSystem K M) (t : K.Carrier) (alpha : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (alpha * logDensity D t x)) ∂(D.omega : Measure M) =
      ∫⁻ x, ENNReal.ofReal (Real.exp ((1 - alpha) * logDensity D (-t) x)) ∂(D.omega : Measure M) := by
  set ω := (D.omega : Measure M)
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-alpha * logDensity D (-t) x))) :=
    (((g66f_log_meas D (-t)).const_mul _).exp).ennreal_ofReal
  have e1 : ∫⁻ x, ENNReal.ofReal (Real.exp ((1 - alpha) * logDensity D (-t) x)) ∂ω =
      ∫⁻ x, (pushedReference D (-t)).rnDeriv ω x *
        ENNReal.ofReal (Real.exp (-alpha * logDensity D (-t) x)) ∂ω := by
    apply lintegral_congr_ae
    filter_upwards [g66f_exp_log D (-t)] with x hx
    rw [hx, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hac : pushedReference D (-t) ≪ ω := (D.equivalent (-t)).1
  rw [e1, lintegral_rnDeriv_mul hac hmeas.aemeasurable]
  unfold pushedReference
  rw [lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [g66f_inv D t] with x hx
  have : logDensity D (-t) (D.flow (-t) x) = - logDensity D t x := by
    have h := hx
    unfold entropyCocycle at h
    rw [h, ← D.flow_add, add_neg_cancel, D.flow_zero]
  rw [this]; congr 2; ring

theorem g66f_es_tri (D : NonsingularSystem K M) (theta : M ≃ᵐ M) (hθ : IsTimeReversal D theta)
    (t : K.Carrier) (alpha : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (alpha * logDensity D (-t) x)) ∂(D.omega : Measure M) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (alpha * logDensity D t x)) ∂(D.omega : Measure M) := by
  obtain ⟨-, hcomm, hpres⟩ := hθ
  have hpush : pushedReference D (-t) = (pushedReference D t).map theta := by
    unfold pushedReference
    conv_lhs => rw [← hpres]
    rw [Measure.map_map (D.flow (-t)).measurable theta.measurable,
      Measure.map_map theta.measurable (D.flow t).measurable]
    congr 1; funext x; exact (hcomm t x).symm
  have hC := theta.measurableEmbedding.rnDeriv_map (pushedReference D t) (D.omega : Measure M)
  rw [hpres] at hC
  conv_lhs => rw [← hpres]
  rw [lintegral_map_equiv]
  apply lintegral_congr_ae
  filter_upwards [hC] with x hx
  unfold logDensity referenceRNReal
  rw [hpush, hx]

theorem g66f_pm (u v : ℝ) (h : v ≤ u) :
    ENNReal.ofReal (-u) + ENNReal.ofReal v ≤ ENNReal.ofReal u + ENNReal.ofReal (-v) := by
  rcases le_total u 0 with hu | hu <;> rcases le_total v 0 with hv | hv
  · rw [ENNReal.ofReal_of_nonpos hv, ENNReal.ofReal_of_nonpos hu, add_zero, zero_add]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have h1 : u = 0 := by linarith
    have h2 : v = 0 := by linarith
    subst h1 h2; simp
  · rw [ENNReal.ofReal_of_nonpos hv, ENNReal.ofReal_of_nonpos (by linarith : -u ≤ 0)]; simp
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -u ≤ 0), ENNReal.ofReal_of_nonpos (by linarith : -v ≤ 0),
      add_zero, zero_add]
    exact ENNReal.ofReal_le_ofReal h

/-- the Gibbs bookkeeping: for r = toReal Delta with ∫ Delta = 1 -/
theorem g66f_vbal (D : NonsingularSystem K M) (t : K.Carrier) :
    ∫⁻ x, ENNReal.ofReal (referenceRNReal D t x - 1) ∂(D.omega : Measure M) =
      ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂(D.omega : Measure M) ∧
    ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂(D.omega : Measure M) ≤ 1 := by
  set ω := (D.omega : Measure M)
  have hrm : Measurable (referenceRNReal D t) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hint : ∫⁻ x, ENNReal.ofReal (referenceRNReal D t x) ∂ω = 1 := by
    have hac : pushedReference D t ≪ ω := (D.equivalent t).1
    have := lintegral_rnDeriv_mul hac (f := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
    have hu : pushedReference D t univ = 1 := by
      unfold pushedReference
      rw [Measure.map_apply (D.flow t).measurable MeasurableSet.univ]; simp
    simp only [mul_one, lintegral_const] at this
    rw [hu, one_mul] at this
    rw [← this]
    apply lintegral_congr_ae
    filter_upwards [g66f_pos D t] with x hx
    unfold referenceRNReal; rw [ENNReal.ofReal_toReal hx.2.ne]
  have hle : ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂ω ≤ 1 := by
    calc ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂ω ≤ ∫⁻ _, 1 ∂ω := by
          apply lintegral_mono; intro x
          have : 0 ≤ referenceRNReal D t x := ENNReal.toReal_nonneg
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
      _ = 1 := by simp
  refine ⟨?_, hle⟩
  have hfin : ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have key : ∫⁻ x, ENNReal.ofReal (referenceRNReal D t x - 1) ∂ω + 1 =
      ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂ω + 1 := by
    calc ∫⁻ x, ENNReal.ofReal (referenceRNReal D t x - 1) ∂ω + 1
        = ∫⁻ x, (ENNReal.ofReal (referenceRNReal D t x - 1) + 1) ∂ω := by
          rw [lintegral_add_right _ measurable_const]; simp
      _ = ∫⁻ x, (ENNReal.ofReal (-(referenceRNReal D t x - 1)) +
            ENNReal.ofReal (referenceRNReal D t x)) ∂ω := by
          apply lintegral_congr; intro x
          have : 0 ≤ referenceRNReal D t x := ENNReal.toReal_nonneg
          rcases le_total (referenceRNReal D t x) 1 with h | h
          · rw [ENNReal.ofReal_of_nonpos (by linarith : referenceRNReal D t x - 1 ≤ 0), zero_add,
              ← ENNReal.ofReal_add (by linarith) this]
            ring_nf; simp
          · rw [ENNReal.ofReal_of_nonpos (by linarith : -(referenceRNReal D t x - 1) ≤ 0), zero_add,
              ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one]
            ring_nf
      _ = _ := by
          have hm : Measurable (fun x => ENNReal.ofReal (-(referenceRNReal D t x - 1))) :=
            ((hrm.sub_const 1).neg).ennreal_ofReal
          rw [lintegral_add_left hm, hint]
  exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp key

theorem g66f_integ (D : NonsingularSystem K M) (u v w z : M → ℝ) (hu : Measurable u) (hv : Measurable v)
    (h : ∀ᵐ x ∂(D.omega : Measure M), ENNReal.ofReal (u x) + ENNReal.ofReal (v x) ≤
      ENNReal.ofReal (w x) + ENNReal.ofReal (z x)) (hw : Measurable w) (hz : Measurable z) :
    ∫⁻ x, ENNReal.ofReal (u x) ∂(D.omega : Measure M) + ∫⁻ x, ENNReal.ofReal (v x) ∂(D.omega : Measure M) ≤
      ∫⁻ x, ENNReal.ofReal (w x) ∂(D.omega : Measure M) + ∫⁻ x, ENNReal.ofReal (z x) ∂(D.omega : Measure M) := by
  rw [← lintegral_add_left hu.ennreal_ofReal, ← lintegral_add_left hw.ennreal_ofReal]
  exact lintegral_mono_ae h

theorem g66f_gibbs1 (D : NonsingularSystem K M) (t : K.Carrier) :
    ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x * logDensity D t x)) ∂(D.omega : Measure M) ≤
      ∫⁻ x, ENNReal.ofReal (referenceRNReal D t x * logDensity D t x) ∂(D.omega : Measure M) ∧
    ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x * logDensity D t x)) ∂(D.omega : Measure M) ≤ 1 := by
  obtain ⟨hbal, hle⟩ := g66f_vbal D t
  have hrm : Measurable (referenceRNReal D t) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hlm := g66f_log_meas D t
  have hpt : ∀ x, referenceRNReal D t x - 1 ≤ referenceRNReal D t x * logDensity D t x := by
    intro x
    have h0 : 0 ≤ referenceRNReal D t x := ENNReal.toReal_nonneg
    rcases h0.lt_or_eq with hp | hz
    · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
      rw [Real.log_inv] at this
      have h2 := mul_le_mul_of_nonneg_left this hp.le
      rw [mul_sub, mul_inv_cancel₀ hp.ne', mul_one] at h2
      unfold logDensity; nlinarith
    · rw [← hz]; simp
  have hI := g66f_integ D (fun x => -(referenceRNReal D t x * logDensity D t x))
    (fun x => referenceRNReal D t x - 1) (fun x => referenceRNReal D t x * logDensity D t x)
    (fun x => -(referenceRNReal D t x - 1)) (hrm.mul hlm).neg (hrm.sub_const 1)
    (ae_of_all _ (fun x => g66f_pm _ _ (hpt x))) (hrm.mul hlm) (hrm.sub_const 1).neg
  try simp only at hI
  rw [hbal] at hI
  have hfin : ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂(D.omega : Measure M) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  refine ⟨(ENNReal.add_le_add_iff_right hfin).mp hI, le_trans ?_ hle⟩
  apply lintegral_mono; intro x
  exact ENNReal.ofReal_le_ofReal (by linarith [hpt x])

theorem g66f_gibbs2 (D : NonsingularSystem K M) (t : K.Carrier) :
    ∫⁻ x, ENNReal.ofReal (logDensity D t x) ∂(D.omega : Measure M) ≤
      ∫⁻ x, ENNReal.ofReal (-logDensity D t x) ∂(D.omega : Measure M) ∧
    ∫⁻ x, ENNReal.ofReal (logDensity D t x) ∂(D.omega : Measure M) ≤ 1 := by
  obtain ⟨hbal, hle⟩ := g66f_vbal D t
  have hrm : Measurable (referenceRNReal D t) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hlm := g66f_log_meas D t
  have hpt : ∀ᵐ x ∂(D.omega : Measure M), logDensity D t x ≤ referenceRNReal D t x - 1 := by
    filter_upwards [g66f_pos D t] with x hx
    exact Real.log_le_sub_one_of_pos (ENNReal.toReal_pos hx.1.ne' hx.2.ne)
  have hI := g66f_integ D (fun x => -(referenceRNReal D t x - 1)) (logDensity D t)
    (fun x => referenceRNReal D t x - 1) (fun x => -logDensity D t x) (hrm.sub_const 1).neg hlm
    (by filter_upwards [hpt] with x hx using g66f_pm _ _ hx) (hrm.sub_const 1) hlm.neg
  try simp only at hI
  rw [hbal] at hI
  have hfin : ∫⁻ x, ENNReal.ofReal (-(referenceRNReal D t x - 1)) ∂(D.omega : Measure M) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  refine ⟨(ENNReal.add_le_add_iff_left hfin).mp hI, le_trans ?_ (hbal ▸ hle)⟩
  apply lintegral_mono_ae
  filter_upwards [hpt] with x hx
  exact ENNReal.ofReal_le_ofReal hx

theorem g66f_tr1 (D : NonsingularSystem K M) (t : K.Carrier) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (s * entropyCocycle D t x) ∂(D.omega : Measure M) =
      ∫⁻ x, ENNReal.ofReal (s * (referenceRNReal D t x * logDensity D t x)) ∂(D.omega : Measure M) := by
  have hm : Measurable (fun y => ENNReal.ofReal (s * logDensity D t y)) :=
    ((g66f_log_meas D t).const_mul s).ennreal_ofReal
  have e : ∫⁻ x, ENNReal.ofReal (s * entropyCocycle D t x) ∂(D.omega : Measure M) =
      ∫⁻ y, ENNReal.ofReal (s * logDensity D t y) ∂(pushedReference D t) := by
    unfold pushedReference; rw [lintegral_map_equiv]; rfl
  have hac : pushedReference D t ≪ (D.omega : Measure M) := (D.equivalent t).1
  rw [e, ← lintegral_rnDeriv_mul hac hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [g66f_pos D t] with x hx
  have h0 : 0 ≤ referenceRNReal D t x := ENNReal.toReal_nonneg
  rw [show s * (referenceRNReal D t x * logDensity D t x) =
    referenceRNReal D t x * (s * logDensity D t x) by ring, ENNReal.ofReal_mul h0]
  unfold referenceRNReal; rw [ENNReal.ofReal_toReal hx.2.ne]

theorem g66f_tr2 (D : NonsingularSystem K M) (t : K.Carrier) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (s * entropyCocycle D t x) ∂(pushedReference D (-t)) =
      ∫⁻ x, ENNReal.ofReal (s * logDensity D t x) ∂(D.omega : Measure M) := by
  unfold pushedReference; rw [lintegral_map_equiv]
  apply lintegral_congr; intro x
  unfold entropyCocycle
  rw [← D.flow_add, add_neg_cancel, D.flow_zero]

theorem g66f_theta (D : NonsingularSystem K M) (theta : M ≃ᵐ M) (hθ : IsTimeReversal D theta)
    (t : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M), logDensity D (-t) (theta x) = logDensity D t x := by
  obtain ⟨-, hcomm, hpres⟩ := hθ
  have hpush : pushedReference D (-t) = (pushedReference D t).map theta := by
    unfold pushedReference
    conv_lhs => rw [← hpres]
    rw [Measure.map_map (D.flow (-t)).measurable theta.measurable,
      Measure.map_map theta.measurable (D.flow t).measurable]
    congr 1; funext x; exact (hcomm t x).symm
  have hC := theta.measurableEmbedding.rnDeriv_map (pushedReference D t) (D.omega : Measure M)
  rw [hpres] at hC
  filter_upwards [hC] with x hx
  unfold logDensity referenceRNReal
  rw [hpush, hx]

theorem g66f_sigma_tri (D : NonsingularSystem K M) (theta : M ≃ᵐ M) (hθ : IsTimeReversal D theta)
    (t : K.Carrier) :
    ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D t (theta x) = -entropyCocycle D t (D.flow (-t) x) := by
  have h1 := g66f_transfer D (-t) (g66f_theta D theta hθ (-t))
  filter_upwards [h1, g66f_inv D t] with x hx1 hx2
  rw [← hx2]
  unfold entropyCocycle
  rw [neg_neg] at hx1
  rw [← hx1, hθ.2.1 (-t) x, neg_neg]

theorem g66f_main (D : NonsingularSystem K M) (t : K.Carrier) :
    0 ≤ QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M)
      (entropyCocycle D t) ∧
    QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (pushedReference D (-t))
      (entropyCocycle D t) ≤ 0 := by
  unfold QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation
  constructor
  · have e1 := g66f_tr1 D t 1
    have e2 := g66f_tr1 D t (-1)
    simp only [one_mul, neg_one_mul] at e1 e2
    rw [e1, e2]
    obtain ⟨h1, h2⟩ := g66f_gibbs1 D t
    rw [EReal.sub_nonneg (Or.inr ?_) (Or.inl (EReal.coe_ennreal_ne_bot _))]
    · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    · exact fun h => (ne_top_of_le_ne_top ENNReal.one_ne_top h2) (EReal.coe_ennreal_eq_top_iff.mp h)
  · have e1 := g66f_tr2 D t 1
    have e2 := g66f_tr2 D t (-1)
    simp only [one_mul, neg_one_mul] at e1 e2
    rw [e1, e2, EReal.sub_nonpos]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (g66f_gibbs2 D t).1

theorem solution (D : NonsingularSystem .discrete M) :
    0 ≤ QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (discreteSigma D) ∧
    QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (pushedReference D (-1 : ℤ)) (discreteSigma D) ≤ 0 ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D theta →
      ∀ᵐ x ∂(D.omega : Measure M),
        discreteSigma D (theta x) = -discreteSigma D (D.flow (-1 : ℤ) x)) := by
  obtain ⟨h1, h2⟩ := g66f_main D (1 : ℤ)
  exact ⟨h1, h2, fun theta hθ => g66f_sigma_tri D theta hθ (1 : ℤ)⟩

end
