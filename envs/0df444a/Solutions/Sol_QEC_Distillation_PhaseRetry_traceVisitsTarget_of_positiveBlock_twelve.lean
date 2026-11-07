-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.traceVisitsTarget_of_positiveBlock_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:21.020416+00:00
-- url     : https://prove2.me/submissions/8665256a-25f1-4dc4-8f30-b18648e2b5d6

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry
import Theorems.Thm_QEC_Distillation_PhaseRetry_blockCoins_allPositive
import Theorems.Thm_QEC_Distillation_PhaseRetry_positiveBlock_visits_target_twelve

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution (start target : ZMod 12) :
    ∀ {blocks : Nat} (trace : BlockTrace 12 blocks) (index : Fin blocks),
      trace index = allPositiveBlock 12 → traceVisitsTarget start target blocks trace := by
  intro blocks
  induction blocks generalizing start with
  | zero =>
      intro trace index
      exact Fin.elim0 index
  | succ blocks ih =>
      intro trace index h
      simp only [traceVisitsTarget]
      revert h
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · intro h
        apply Or.inl
        rw [h, blockCoins_allPositive]
        exact positiveBlock_visits_target_twelve start target
      · intro h
        apply Or.inr
        apply ih (start := blockEndpoint start (trace 0))
          (trace := fun inner => trace inner.succ) (index := tailIndex)
        simpa using h
end QEC.Distillation.PhaseRetry
