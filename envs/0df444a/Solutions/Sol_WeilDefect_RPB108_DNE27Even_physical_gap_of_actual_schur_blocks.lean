-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.physical_gap_of_actual_schur_blocks
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:05:17.194828+00:00
-- url     : https://prove2.me/submissions/cc898be9-10ce-45f4-b9bd-e2fa0a19152f

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_actual_low_schur_lower
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_actual_retained_schur_lower
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_form_blocks
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
import Definitions.Def_RPB108_DNE27SchurBounds_Even
import Definitions.Def_RPB108_DNE27SourcePairing_Even
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108
open WeilDefect.RPB108.DNE27Even

theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E → ℝ) (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hsym : ∀ u v, (B u v).re = (B v u).re)
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
    (hraw : Q ((∑ i, z i • x i)+(h-T (∑ i, z i • source i))) =
      N+2*(inner ℂ (∑ i, z i • source i) (h-T (∑ i, z i • source i))).re+
      (B (h-T (∑ i, z i • source i)) (h-T (∑ i, z i • source i))).re)
    (hfinite : N-(inner ℂ (∑ i, z i • source i)
      (T (∑ i, z i • source i))).re =
      actualLowSchur T source lowDiag*‖z 0‖^2+
      2*(star (z 0)*(nativePairing a z-inverseSourcePairing T source z)).re+
      actualRetainedSchur T source V G z)
    (hhigh : highFloor*‖h‖^2 ≤ (B h h).re) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤
      Q ((∑ i, z i • (x i-T (source i)))+h) := by
  exact physical_gap_of_form_blocks Q B T hleft hright hsym x source hT hx hsource
    V G hV hG hGram a ha z h N (actualLowSchur T source lowDiag)
    (actualRetainedSchur T source V G z) hsolve hraw hfinite
    (actual_low_schur_lower T source lowDiag hT (hsource 0) hlow)
    (actual_retained_schur_lower T source V G hT hGram z) hhigh
