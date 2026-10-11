-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.physical_gap_of_form_blocks
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:03:21.510863+00:00
-- url     : https://prove2.me/submissions/124654af-4db0-4f40-be68-c690815ef0bf

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_realized_source_gram
import Theorems.Thm_WeilDefect_RPB108_completed_column_identity
import Theorems.Thm_WeilDefect_RPB108_energy_lower_of_form_blocks
import Mathlib
import Definitions.Def_RPB108_DNE27Gram_Even
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
import Definitions.Def_RPB108_DNE27Numerics_Even
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
    (z : Fin 4 → ℂ) (h : E) (N D actualRetained : ℝ)
    (hsolve : ∀ u, B (T (∑ i, z i • source i)) u =
      inner ℂ (∑ i, z i • source i) u)
    (hraw : Q ((∑ i, z i • x i)+(h-T (∑ i, z i • source i))) =
      N+2*(inner ℂ (∑ i, z i • source i) (h-T (∑ i, z i • source i))).re+
      (B (h-T (∑ i, z i • source i)) (h-T (∑ i, z i • source i))).re)
    (hfinite : N-(inner ℂ (∑ i, z i • source i)
      (T (∑ i, z i • source i))).re =
      D*‖z 0‖^2+2*(star (z 0)*(nativePairing a z-inverseSourcePairing T source z)).re+
      actualRetained)
    (hD : nativeLow ≤ D)
    (hretained : complexGram V (fun i => (gramScales i : ℂ)*z i.succ) ≤ actualRetained)
    (hhigh : highFloor*‖h‖^2 ≤ (B h h).re) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤
      Q ((∑ i, z i • (x i-T (source i)))+h) := by
  apply physical_gap_of_realized_source_gram T x source hT hx hsource V G hV hG hGram a ha
    z h (Q ((∑ i, z i • (x i-T (source i)))+h))
  have hraw' := hraw
  rw [← completed_column_identity T x source z h] at hraw'
  exact energy_lower_of_form_blocks B T hleft hright hsym
    (∑ i, z i • source i) h hsolve N D _ actualRetained nativeLow highFloor _
    (z 0) (nativePairing a z) (inverseSourcePairing T source z)
    hraw' hfinite hD hretained hhigh
