-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.physical_gap_of_native_form_blocks
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:31:22.25693+00:00
-- url     : https://prove2.me/submissions/946bac6f-5c6f-4b3f-9d23-5859b159d3e4

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_finite_schur_identity_of_native_block
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_physical_gap_of_actual_schur_blocks
import Theorems.Thm_WeilDefect_RPB108_inverse_covariance_hermitian
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27NativePairing_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_DNE27SchurBounds_Odd
import Definitions.Def_RPB108_DNE27SourcePairing_Odd
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Odd

theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E → ℝ) (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hherm : ∀ u v, B u v = star (B v u))
    (x source : Fin 4 → E)
    (hT : ‖T‖ ≤ 1/highFloor)
    (hx : ∀ i, ‖x i‖ ≤ nativeMass i)
    (hsource : ∀ i, ‖source i‖^2 ≤ sourceSquare i)
    (V G : Fin 3 → Fin 3 → ℝ)
    (hV : ∀ i j, nativeLower i j ≤ V i j ∧ V i j ≤ nativeUpper i j)
    (hG : ∀ i j, gramLower i j ≤ G i j ∧ G i j ≤ gramUpper i j)
    (hGram : ∀ i j, inner ℂ (source i.succ) (source j.succ) =
      ((gramScales i*gramScales j*G i j : ℝ) : ℂ))
    (a : Fin 3 → ℝ)
    (ha : ∀ i, nativePairingLower i ≤ a i ∧ a i ≤ nativePairingUpper i)
    (z : Fin 4 → ℂ) (h : E) (N lowDiag : ℝ)
    (hlow : lowNativeLower ≤ lowDiag)
    (hsolve : ∀ u, B (T (∑ i, z i • source i)) u =
      inner ℂ (∑ i, z i • source i) u)
    (hsolveLow : ∀ u, B (T (source 0)) u = inner ℂ (source 0) u)
    (hsolveRetained : ∀ u, B (T (∑ i : Fin 3, z i.succ • source i.succ)) u =
      inner ℂ (∑ i : Fin 3, z i.succ • source i.succ) u)
    (hraw : Q ((∑ i, z i • x i)+(h-T (∑ i, z i • source i))) =
      N+2*(inner ℂ (∑ i, z i • source i) (h-T (∑ i, z i • source i))).re+
      (B (h-T (∑ i, z i • source i)) (h-T (∑ i, z i • source i))).re)
    (hnative : N = lowDiag*‖z 0‖^2+2*(star (z 0)*nativePairing a z).re+
      retainedNativeEnergy V G z)
    (hhigh : highFloor*‖h‖^2 ≤ (B h h).re) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤
      Q ((∑ i, z i • (x i-T (source i)))+h) := by
  have hsym (u v : E) : (B u v).re = (B v u).re := by rw [hherm]; simp
  have hc := inverse_covariance_hermitian B T hherm (source 0)
    (∑ i : Fin 3, z i.succ • source i.succ) (hsolveLow _) (hsolveRetained _)
  have hf := finite_schur_identity_of_native_block T source V G a z N lowDiag hc hnative
  exact physical_gap_of_actual_schur_blocks Q B T hleft hright hsym x source hT hx hsource
    V G hV hG hGram a ha z h N lowDiag hlow hsolve hraw hf hhigh
