-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.finite_schur_identity_of_native_block
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T05:29:52.987029+00:00
-- url     : https://prove2.me/submissions/b48ad230-8af9-44bf-964c-a47592a999ab

import Theorems.Thm_WeilDefect_RPB108_finite_schur_split
import Mathlib
import Definitions.Def_RPB108_DNE27NativePairing_Odd
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
    (T : E →L[ℂ] E) (source : Fin 4 → E) (V G : Fin 3 → Fin 3 → ℝ)
    (a : Fin 3 → ℝ) (z : Fin 4 → ℂ) (N lowDiag : ℝ)
    (hcov : inner ℂ (∑ i : Fin 3, z i.succ • source i.succ) (T (source 0)) =
      star (inner ℂ (source 0) (T (∑ i : Fin 3, z i.succ • source i.succ))))
    (hnative : N = lowDiag*‖z 0‖^2+2*(star (z 0)*nativePairing a z).re+
      retainedNativeEnergy V G z) :
    N-(inner ℂ (∑ i, z i • source i) (T (∑ i, z i • source i))).re =
      actualLowSchur T source lowDiag*‖z 0‖^2+
      2*(star (z 0)*(nativePairing a z-inverseSourcePairing T source z)).re+
      actualRetainedSchur T source V G z := by
  have h := finite_schur_split T (source 0)
    (∑ i : Fin 3, z i.succ • source i.succ) (z 0) (nativePairing a z)
    N lowDiag (retainedNativeEnergy V G z) hcov hnative
  simpa only [Fin.sum_univ_succ, actualLowSchur, inverseSourcePairing,
    actualRetainedSchur] using h
