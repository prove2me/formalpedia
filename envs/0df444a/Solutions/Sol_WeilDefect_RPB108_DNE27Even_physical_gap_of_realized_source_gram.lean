-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.physical_gap_of_realized_source_gram
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:39:36.648795+00:00
-- url     : https://prove2.me/submissions/8daca341-a11f-475a-9d61-82e9982e0f7c

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_inverse_source_pairing_square_of_gram
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_physical_gap_of_native_row_enclosures
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
    (T : E →L[ℂ] E) (x source : Fin 4 → E)
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
    (z : Fin 4 → ℂ) (h : E) (energy : ℝ)
    (hcompletion : nativeLow*‖z 0‖^2-
      2*‖z 0‖*‖nativePairing a z-inverseSourcePairing T source z‖+
      complexGram V (fun i => (gramScales i : ℂ)*z i.succ)+
      highFloor*‖h‖^2 ≤ energy) :
    (4/(10^36) : ℝ)*‖(∑ i, z i • (x i-T (source i)))+h‖^2 ≤ energy := by
  exact physical_gap_of_native_row_enclosures T x source hT hx hsource V G hV hG a ha
    z h energy (inverseSourcePairing T source z)
    (inverse_source_pairing_square_of_gram T source G hT (hsource 0) hGram z) hcompletion
