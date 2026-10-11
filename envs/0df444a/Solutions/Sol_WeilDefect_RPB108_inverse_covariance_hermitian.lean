-- Prove2me | solution 1 for WeilDefect.RPB108.inverse_covariance_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:24:55.36986+00:00
-- url     : https://prove2.me/submissions/0aac8b2e-d0ab-4ad3-b555-6a9132abe972

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hherm : ∀ u v, B u v = star (B v u)) (r v : E)
    (hr : B (T r) (T v) = inner ℂ r (T v))
    (hv : B (T v) (T r) = inner ℂ v (T r)) :
    inner ℂ v (T r) = star (inner ℂ r (T v)) := by
  rw [← hv, ← hr]
  exact hherm _ _
