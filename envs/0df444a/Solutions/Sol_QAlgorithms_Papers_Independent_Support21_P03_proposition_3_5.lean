-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:58:45.164185+00:00
-- url     : https://prove2.me/submissions/33255ccb-e237-4c6c-97a4-beaa51a3bbdd

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

theorem solution (D : NonsingularSystem K M) :
    (∀ t alpha, finiteES D t alpha = finiteES D (-t) (1 - alpha)) ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D theta →
      ∀ t alpha, finiteES D (-t) alpha = finiteES D t alpha ∧
        finiteES D t alpha = finiteES D t (1 - alpha)) := by
  have h1 : ∀ t alpha, finiteES D t alpha = finiteES D (-t) (1 - alpha) := by
    intro t alpha; unfold finiteES; rw [g66f_es_sym]
  refine ⟨h1, fun theta hθ t alpha => ⟨?_, ?_⟩⟩
  · unfold finiteES; rw [g66f_es_tri D theta hθ]
  · rw [h1]; unfold finiteES; rw [g66f_es_tri D theta hθ]

end
