-- Prove2me | solution 1 for P2M_GlobalTheory_Lin_NonPrimeVonMangoldt_F__eq_3cd59a318829
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:02.361804+00:00
-- url     : https://prove2.me/submissions/0b506d5b-6baa-40e4-9cc4-75646af68dc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.NonPrimeVonMangoldt
namespace GlobalTheory.Lin.NonPrimeVonMangoldt
theorem _root_.solution (p : Nat.Primes) (k : ℕ) :
    F₂ (p, k) = Real.log p / ((p : ℝ) ^ (k + 2)) ^ (3 / 4 : ℝ) := by
  simp only [F₂, Function.comp_apply, F₁, F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm, Nat.cast_pow]
end GlobalTheory.Lin.NonPrimeVonMangoldt
