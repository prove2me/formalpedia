-- Prove2me | solution 1 for WeilDefect.RPB108.sesquilinear_source_coupling
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:24:48.632772+00:00
-- url     : https://prove2.me/submissions/ae1ae1ad-cf59-4c46-8101-774e42434975

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (x source : Fin 4 → E) (z : Fin 4 → ℂ) (v : E)
    (hc : ∀ i, F (x i) v = inner ℂ (source i) v) :
    F (∑ i, z i • x i) v = inner ℂ (∑ i, z i • source i) v := by
  simp only [LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, smul_eq_mul, hc,
    sum_inner, inner_smul_left]
