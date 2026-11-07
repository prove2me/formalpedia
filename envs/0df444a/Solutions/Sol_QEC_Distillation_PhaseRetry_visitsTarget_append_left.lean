-- Prove2me | solution 1 for QEC.Distillation.PhaseRetry.visitsTarget_append_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:19:55.94321+00:00
-- url     : https://prove2.me/submissions/d0f608c1-1160-43d3-b86d-9609a0018f55

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
    (h : visitsTarget start target history) :
    visitsTarget start target (history ++ suffix) := by
  induction history generalizing start with
  | nil =>
      unfold visitsTarget at h ⊢
      change target ∈ [start] at h
      change target ∈ positions start suffix
      rw [List.mem_singleton] at h
      subst target
      induction suffix with
      | nil => simp [positions]
      | cons coin tail ih => simp [positions]
  | cons coin tail ih =>
      unfold visitsTarget at h ⊢
      change target ∈ start :: positions (start + signedIncrement coin) tail at h
      change target ∈ start :: positions (start + signedIncrement coin) (tail ++ suffix)
      simp only [List.mem_cons] at h ⊢
      exact h.elim Or.inl (fun h' => Or.inr (ih h'))
end QEC.Distillation.PhaseRetry
