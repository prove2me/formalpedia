-- Prove2me | solution 1 for condRevenue_eq_integral_prefix_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:53:00.815466+00:00
-- url     : https://prove2.me/submissions/df3370cd-a5ed-44fe-a615-8b0cdd59326c

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (U : Ω → Finset.Icc 1 k → ℝ)
    (rebuild : ℝ × (Finset.Icc 1 k → ℝ) → ℕ → ℝ)
    (hU : Measurable U)
    (hJoint : ∀ s, Measurable (fun z => revenue f p (rebuild z) (k + 1) s))
    (hUpdate : ∀ ω y s,
      revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
        revenue f p (rebuild (y, U ω)) (k + 1) s)
    (y s : ℝ) :
    ∫ u, revenue f p (rebuild (y, u)) (k + 1) s ∂Measure.map U P =
      condRevenue P X f p (k + 1) y s := by
  have hSectionMeas :
      Measurable (fun u : Finset.Icc 1 k → ℝ =>
        revenue f p (rebuild (y, u)) (k + 1) s) :=
    (hJoint s).comp (Measurable.prodMk measurable_const measurable_id)
  unfold condRevenue
  calc
    _ = ∫ ω, revenue f p (rebuild (y, U ω)) (k + 1) s ∂P := by
      rw [integral_map hU.aemeasurable hSectionMeas.aestronglyMeasurable]
    _ = ∫ ω, revenue f p
        (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => (hUpdate ω y s).symm)
