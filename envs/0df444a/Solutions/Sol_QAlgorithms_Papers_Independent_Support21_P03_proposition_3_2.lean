-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:27:26.986569+00:00
-- url     : https://prove2.me/submissions/660a25b8-f07f-46d7-8f63-ea64b9ab7ade

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.2, PDF p.9, equation (3.4). -/
theorem solution (D : NonsingularSystem K M) (theta : M ≃ᵐ M)
    (hTRI : IsTimeReversal D theta) :
    ∀ t, ∀ᵐ x ∂(D.omega : Measure M),
      entropyCocycle D t (theta x) = entropyCocycle D (-t) x := by
  intro t
  obtain ⟨_, hcomm, hpres⟩ := hTRI
  have hprob : ∀ s, IsProbabilityMeasure (pushedReference D s) := fun s =>
    Measure.isProbabilityMeasure_map (D.flow s).measurable.aemeasurable
  have hc : ∀ x, D.flow t (theta x) = theta (D.flow (-t) x) := by
    intro x; rw [hcomm (-t) x, neg_neg]
  have hmap : (pushedReference D (-t)).map theta = pushedReference D t := by
    unfold pushedReference
    rw [Measure.map_map theta.measurable (D.flow (-t)).measurable]
    have : (theta ∘ D.flow (-t)) = (D.flow t) ∘ theta := by funext x; simp [hc]
    rw [this, ← Measure.map_map (D.flow t).measurable theta.measurable, hpres]
  have key : ∀ᵐ y ∂(D.omega : Measure M),
      (pushedReference D t).rnDeriv (D.omega : Measure M) (theta y) =
        (pushedReference D (-t)).rnDeriv (D.omega : Measure M) y := by
    have h := theta.measurableEmbedding.rnDeriv_map (pushedReference D (-t)) (D.omega : Measure M)
    rw [hmap, hpres] at h
    exact h
  have hq : Measure.QuasiMeasurePreserving (D.flow (-t)) (D.omega : Measure M) (D.omega : Measure M) :=
    ⟨(D.flow (-t)).measurable, (D.equivalent (-t)).1⟩
  filter_upwards [hq.ae key] with x hx
  simp only [entropyCocycle, logDensity, referenceRNReal]
  rw [hc, hx]
