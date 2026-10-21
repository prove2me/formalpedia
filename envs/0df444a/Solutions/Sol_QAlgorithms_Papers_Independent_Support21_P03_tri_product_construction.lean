-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.tri_product_construction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:27:45.530606+00:00
-- url     : https://prove2.me/submissions/6f144bc1-f881-4584-b675-79c6d632fff1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

theorem g66c_measurable_neg (K : TimeKind) : Measurable (fun t : K.Carrier => -t) := by
  cases K
  · exact measurable_from_top
  · show Measurable (fun t : ℝ => -t)
    exact measurable_neg

def g66c_prodSys (D : NonsingularSystem K M) : NonsingularSystem K (M × M) where
  flow t := MeasurableEquiv.prodCongr (D.flow t) (D.flow (-t))
  flow_zero z := by
    obtain ⟨a, b⟩ := z
    change (D.flow 0 a, D.flow (-0) b) = (a, b)
    rw [neg_zero, D.flow_zero, D.flow_zero]
  flow_add t s z := by
    obtain ⟨a, b⟩ := z
    change (D.flow (t + s) a, D.flow (-(t + s)) b) =
      (D.flow t (D.flow s a), D.flow (-t) (D.flow (-s) b))
    rw [D.flow_add, neg_add, D.flow_add]
  jointly_measurable := by
    have h1 : Measurable (fun z : K.Carrier × (M × M) => D.flow z.1 z.2.1) :=
      D.jointly_measurable.comp (measurable_fst.prodMk measurable_snd.fst)
    have h2 : Measurable (fun z : K.Carrier × (M × M) => D.flow (-z.1) z.2.2) :=
      D.jointly_measurable.comp (((g66c_measurable_neg K).comp measurable_fst).prodMk
        measurable_snd.snd)
    exact h1.prodMk h2
  omega := ⟨(D.omega : Measure M).prod (D.omega : Measure M), inferInstance⟩
  equivalent t := by
    have hmap : Measure.map (MeasurableEquiv.prodCongr (D.flow t) (D.flow (-t)))
        ((D.omega : Measure M).prod (D.omega : Measure M)) =
        (Measure.map (D.flow t) (D.omega : Measure M)).prod
          (Measure.map (D.flow (-t)) (D.omega : Measure M)) := by
      rw [Measure.map_prod_map _ _ (D.flow t).measurable (D.flow (-t)).measurable]
      rfl
    simp only [ProbabilityMeasure.coe_mk]
    rw [hmap]
    exact ⟨(D.equivalent t).1.prod (D.equivalent (-t)).1,
      (D.equivalent t).2.prod (D.equivalent (-t)).2⟩

theorem solution (D : NonsingularSystem K M) :
    ∃ P : NonsingularSystem K (M × M),
      (∀ t z, P.flow t z = (D.flow t z.1, D.flow (-t) z.2)) ∧
      (P.omega : Measure (M × M)) = (D.omega : Measure M).prod (D.omega : Measure M) ∧
      IsTimeReversal P (MeasurableEquiv.prodComm : (M × M) ≃ᵐ (M × M)) := by
  refine ⟨g66c_prodSys D, fun t z => rfl, rfl, ?_, ?_, ?_⟩
  · intro z; simp [MeasurableEquiv.prodComm]
  · intro t z
    obtain ⟨a, b⟩ := z
    change (D.flow (-t) b, D.flow t a) = (D.flow (-t) b, D.flow (-(-t)) a)
    rw [neg_neg]
  · show Measure.map MeasurableEquiv.prodComm ((D.omega : Measure M).prod (D.omega : Measure M)) =
      (D.omega : Measure M).prod (D.omega : Measure M)
    exact Measure.prod_swap

end
