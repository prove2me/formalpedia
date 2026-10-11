-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.physical_gap_of_sesquilinear_realization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:35:30.454325+00:00
-- url     : https://prove2.me/submissions/6a602bde-611c-4376-bd65-4fbb292b999c

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_native_block_of_sesquilinear_entries
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_physical_gap_of_native_form_blocks
import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_raw_block_of_sesquilinear_coupling
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Odd
import Definitions.Def_RPB108_DNE27NativePairing_Odd
import Definitions.Def_RPB108_DNE27Numerics_Odd
import Definitions.Def_RPB108_DNE27SchurBounds_Odd
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
    (F : E →ₛₗ[starRingEnd ℂ] E →ₗ[ℂ] ℂ)
    (hFherm : ∀ u v, F u v = star (F v u))
    (Q : E → ℝ) (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hBherm : ∀ u v, B u v = star (B v u))
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
    (z : Fin 4 → ℂ) (h : E) (lowDiag : ℝ)
    (hlow : lowNativeLower ≤ lowDiag)
    (hd : (F (x 0) (x 0)).re = lowDiag)
    (hrow : ∀ i : Fin 3, F (x 0) (x i.succ) = ((gramScales i*a i : ℝ) : ℂ))
    (hret : ∀ i j : Fin 3, F (x i.succ) (x j.succ) =
      ((gramScales i*gramScales j*(V i j+G i j/highFloor) : ℝ) : ℂ))
    (hsolve : ∀ u, B (T (∑ i, z i • source i)) u =
      inner ℂ (∑ i, z i • source i) u)
    (hsolveLow : ∀ u, B (T (source 0)) u = inner ℂ (source 0) u)
    (hsolveRetained : ∀ u, B (T (∑ i : Fin 3, z i.succ • source i.succ)) u =
      inner ℂ (∑ i : Fin 3, z i.succ • source i.succ) u)
    (hQ : Q ((∑ i, z i • x i)+(h-T (∑ i, z i • source i))) =
      (F ((∑ i, z i • x i)+(h-T (∑ i, z i • source i)))
        ((∑ i, z i • x i)+(h-T (∑ i, z i • source i)))).re)
    (hc : ∀ i, F (x i) (h-T (∑ j, z j • source j)) =
      inner ℂ (source i) (h-T (∑ j, z j • source j)))
    (hhighRestriction : (F (h-T (∑ i, z i • source i))
      (h-T (∑ i, z i • source i))).re =
      (B (h-T (∑ i, z i • source i)) (h-T (∑ i, z i • source i))).re)
    (hhigh : highFloor*‖h‖^2 ≤ (B h h).re) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤
      Q ((∑ i, z i • (x i-T (source i)))+h) := by
  exact physical_gap_of_native_form_blocks Q B T hleft hright hBherm x source hT hx hsource
    V G hV hG hGram a ha z h (F (∑ i, z i • x i) (∑ i, z i • x i)).re lowDiag hlow
    hsolve hsolveLow hsolveRetained
    (raw_block_of_sesquilinear_coupling F hFherm Q B x source z _ hQ hc hhighRestriction)
    (native_block_of_sesquilinear_entries F hFherm x V G a lowDiag hd hrow hret z) hhigh
