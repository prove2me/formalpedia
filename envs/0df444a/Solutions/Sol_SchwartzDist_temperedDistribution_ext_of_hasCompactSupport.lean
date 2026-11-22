-- Prove2me | solution 1 for SchwartzDist.temperedDistribution_ext_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:39:05.17079+00:00
-- url     : https://prove2.me/submissions/ced0aff4-ec90-4298-9d54-8a8e2e07b232

import Mathlib
import Theorems.Thm_SchwartzDist_dense_setOf_hasCompactSupport

open SchwartzMap LineDeriv Topology Filter

set_option autoImplicit false

open SchwartzDist

theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T₁ T₂ : 𝓢'(E, F))
    (h : ∀ φ : 𝓢(E, ℂ), HasCompactSupport (φ : E → ℂ) → T₁ φ = T₂ φ) :
    T₁ = T₂ := by
  -- the compactly supported Schwartz functions are dense in `𝓢(E, ℂ)`
  have hd : Dense {f : 𝓢(E, ℂ) | HasCompactSupport (f : E → ℂ)} :=
    SchwartzDist.dense_setOf_hasCompactSupport (E := E) (F := ℂ)
  -- a tempered distribution is a continuous map on `𝓢(E, ℂ)`
  have hc₁ : Continuous (fun φ : 𝓢(E, ℂ) => T₁ φ) :=
    (T₁ : 𝓢(E, ℂ) →L[ℂ] F).continuous
  have hc₂ : Continuous (fun φ : 𝓢(E, ℂ) => T₂ φ) :=
    (T₂ : 𝓢(E, ℂ) →L[ℂ] F).continuous
  -- two continuous maps into a Hausdorff space agreeing on a dense set are equal
  have heq : (fun φ : 𝓢(E, ℂ) => T₁ φ) = fun φ => T₂ φ :=
    Continuous.ext_on hd hc₁ hc₂ (fun φ hφ => h φ hφ)
  exact ContinuousLinearMap.ext (fun φ => congrFun heq φ)
