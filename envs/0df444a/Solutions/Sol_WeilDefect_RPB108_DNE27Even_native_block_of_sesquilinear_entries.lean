-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.native_block_of_sesquilinear_entries
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:30:35.063857+00:00
-- url     : https://prove2.me/submissions/1b9d4168-b125-4f6c-82b5-7aacd3c8c963

import Theorems.Thm_WeilDefect_RPB108_hermitian_form_add
import Theorems.Thm_WeilDefect_RPB108_scaled_gram_difference
import Theorems.Thm_WeilDefect_RPB108_sesquilinear_gram
import Theorems.Thm_WeilDefect_RPB108_sesquilinear_smul_diagonal
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
import Definitions.Def_RPB108_DNE27SchurBounds_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

namespace WeilDefect.RPB108
/-- Exact column congruence for the retained quadratic form. -/
theorem scaled_retained_gram (V : Fin 3 → Fin 3 → ℝ) (s : Fin 3 → ℝ)
    (z : Fin 3 → ℂ) :
    complexGram (fun i j => s i*s j*V i j) z =
      complexGram V (fun i => (s i : ℂ)*z i) := by
  simpa [complexGram] using scaled_gram_difference V (fun _ _ => 0) s 1 z
end WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hherm : ∀ u v, F u v = star (F v u)) (x : Fin 4 → E)
    (V G : Fin 3 → Fin 3 → ℝ) (a : Fin 3 → ℝ) (lowDiag : ℝ)
    (hd : (F (x 0) (x 0)).re = lowDiag)
    (hrow : ∀ i : Fin 3, F (x 0) (x i.succ) = ((gramScales i*a i : ℝ) : ℂ))
    (hret : ∀ i j : Fin 3, F (x i.succ) (x j.succ) =
      ((gramScales i*gramScales j*(V i j+G i j/highFloor) : ℝ) : ℂ))
    (z : Fin 4 → ℂ) :
    (F (∑ i, z i • x i) (∑ i, z i • x i)).re =
      lowDiag*‖z 0‖^2+2*(star (z 0)*nativePairing a z).re+retainedNativeEnergy V G z := by
  have hs : (∑ i, z i • x i) = z 0 • x 0+(∑ i : Fin 3, z i.succ • x i.succ) :=
    Fin.sum_univ_succ _
  have hc : F (z 0 • x 0) (∑ i : Fin 3, z i.succ • x i.succ) =
      star (z 0)*nativePairing a z := by
    rw [LinearMap.map_smulₛₗ₂]
    simp only [map_sum, map_smul, smul_eq_mul, hrow]
    change star (z 0)*(∑ i : Fin 3, z i.succ*((gramScales i*a i : ℝ) : ℂ)) = _
    congr 1
    unfold nativePairing
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hg := sesquilinear_gram F (fun i : Fin 3 => x i.succ)
    (fun i j => gramScales i*gramScales j*(V i j+G i j/highFloor)) hret
    (fun i => z i.succ)
  have hr : (F (∑ i : Fin 3, z i.succ • x i.succ)
      (∑ i : Fin 3, z i.succ • x i.succ)).re = retainedNativeEnergy V G z := by
    simpa only [retainedNativeEnergy, scaled_retained_gram] using hg
  rw [hs, hermitian_form_add F hherm, sesquilinear_smul_diagonal, hd, hc, hr]
  ring
