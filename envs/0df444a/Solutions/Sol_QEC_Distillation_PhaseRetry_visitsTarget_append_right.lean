-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.visitsTarget_append_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:39:06.044256+00:00
-- url     : https://prove2.me/submissions/7473c051-8ba7-45e5-95c5-01fb38177b4d

import Mathlib.Probability.Distributions.Uniform
import Definitions.Def_QEC_Distillation_Injection_PhaseRetry

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.PhaseRetry
noncomputable section
namespace QEC.Distillation.PhaseRetry
theorem _root_.solution {q : Nat} {start target : ZMod q}
    (history suffix : List Bool)
    (h : visitsTarget (endpoint start history) target suffix) :
    visitsTarget start target (history ++ suffix) := by
  induction history generalizing start with
  | nil => simpa [endpoint] using h
  | cons coin tail ih =>
      unfold visitsTarget at h ⊢
      change target ∈ start :: positions (start + signedIncrement coin) (tail ++ suffix)
      simp only [List.mem_cons]
      apply Or.inr
      exact ih (by simpa only [visitsTarget, endpoint] using h)
end QEC.Distillation.PhaseRetry
