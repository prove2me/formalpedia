-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:55:23.406649+00:00
-- url     : https://prove2.me/submissions/6c14160a-38d8-4957-ac1f-55ddfa95f08f

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

theorem solution (D : NonsingularSystem K M) :
    (∀ t s, ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D (t + s) x = entropyCocycle D s x + entropyCocycle D t (D.flow s x)) ∧
    (∀ᵐ x ∂(D.omega : Measure M), entropyCocycle D 0 x = 0) ∧
    (∀ t, ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D (-t) x = -entropyCocycle D t (D.flow (-t) x)) := by
  refine ⟨g66f_cocycle D, g66f_zero D, fun t => ?_⟩
  filter_upwards [g66f_cocycle D t (-t), g66f_zero D] with x h1 h2
  rw [add_neg_cancel, h2] at h1
  linarith

end
