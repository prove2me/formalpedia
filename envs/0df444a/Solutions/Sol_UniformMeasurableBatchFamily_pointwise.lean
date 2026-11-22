-- Prove2me | solution 1 for UniformMeasurableBatchFamily.pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:59.656313+00:00
-- url     : https://prove2.me/submissions/9eb76f2c-3043-460a-9b39-17cd7d2c7d32

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure

set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
namespace UniformMeasurableBatchFamily
theorem _root_.solution
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) [hL : UniformMeasurableBatchFamily L]
    (n : ℕ) : MeasurableBatchLearner X (L n) where
  eval_measurable m :=
    (hL.eval_measurable m).comp (Measurable.prodMk measurable_const measurable_id)
end UniformMeasurableBatchFamily
