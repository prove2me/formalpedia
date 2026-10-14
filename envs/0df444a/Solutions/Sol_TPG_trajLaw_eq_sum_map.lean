-- Prove2me | solution 1 for TPG.trajLaw_eq_sum_map
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:48:32.684984+00:00
-- url     : https://prove2.me/submissions/5ccc02ef-4b3d-45cb-9b9c-6b01eae8e741

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-- With the state and the action frozen, the single-step law is the push-forward of the reward
law under the embedding `y ↦ (a, b, y)`. -/
private lemma TPG_dirac_prod_dirac_prod {S : Type} [MeasurableSpace S] (a : S) (b : Bool)
    (ν : Measure ℝ) [SFinite ν] :
    (Measure.dirac a).prod ((Measure.dirac b).prod ν)
      = ν.map (fun y : ℝ => ((a, b, y) : S × Bool × ℝ)) := by
  rw [Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map measurable_prodMk_left measurable_prodMk_left]
  rfl

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T : ℕ) (q : ℕ → ℝ) :
    E.trajLaw T q
      = ∑ p : (Fin T → S) × (Fin T → Bool),
          ENNReal.ofReal (E.pathWeight T q p.1 p.2) •
            (E.rewardLaw p.1 p.2).map (embedPath p.1 p.2) := by
  unfold Env.trajLaw
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have hmeas : ∀ t : Fin T,
      Measurable (fun y : ℝ => ((p.1 t, p.2 t, y) : S × Bool × ℝ)) := fun t =>
    measurable_prodMk_left.comp measurable_prodMk_left
  have : ∀ t : Fin T, IsProbabilityMeasure
      ((E.R (p.1 t) (p.2 t)).map (fun y : ℝ => ((p.1 t, p.2 t, y) : S × Bool × ℝ))) := fun t =>
    Measure.isProbabilityMeasure_map (hmeas t).aemeasurable
  have hpi := Measure.pi_map_pi (μ := fun t : Fin T => E.R (p.1 t) (p.2 t))
    (f := fun (t : Fin T) (y : ℝ) => ((p.1 t, p.2 t, y) : S × Bool × ℝ))
    (fun t => (hmeas t).aemeasurable)
  simp only [TPG_dirac_prod_dirac_prod]
  exact hpi.symm
