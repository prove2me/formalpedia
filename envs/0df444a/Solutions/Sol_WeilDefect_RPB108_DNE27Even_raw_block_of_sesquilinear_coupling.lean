-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.raw_block_of_sesquilinear_coupling
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:27:40.711037+00:00
-- url     : https://prove2.me/submissions/4d23d071-577b-431b-8667-8bc0c38eb714

import Theorems.Thm_WeilDefect_RPB108_hermitian_form_add
import Theorems.Thm_WeilDefect_RPB108_sesquilinear_source_coupling
import Mathlib
import Definitions.Def_RPB108_DNE27SchurBounds_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ u v, F u v = star (F v u)) (Q : E → ℝ) (B : E → E → ℂ)
    (x source : Fin 4 → E) (z : Fin 4 → ℂ) (v : E)
    (hQ : Q ((∑ i, z i • x i)+v) =
      (F ((∑ i, z i • x i)+v) ((∑ i, z i • x i)+v)).re)
    (hc : ∀ i, F (x i) v = inner ℂ (source i) v)
    (hhigh : (F v v).re = (B v v).re) :
    Q ((∑ i, z i • x i)+v) = (F (∑ i, z i • x i) (∑ i, z i • x i)).re+
      2*(inner ℂ (∑ i, z i • source i) v).re+(B v v).re := by
  rw [hQ, hermitian_form_add F hherm, sesquilinear_source_coupling F x source z v hc, hhigh]
