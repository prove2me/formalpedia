-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_weight_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:08:06.371477+00:00
-- url     : https://prove2.me/submissions/6a05df63-4b11-4694-83ba-592dbdb5df7d

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    ∀ b : Sum (Fin 4) QuadraticIndex → Bit,
      HammingWeight (l2CoefficientMap b) % 2 = 0 := by
  intro b
  have hweight (v : Word) : (HammingWeight v : Bit) = wordPairing allOnes v := by
    classical
    simp only [HammingWeight, hammingSupport, Finset.card_eq_sum_ones, Nat.cast_sum,
      Nat.cast_one, Finset.sum_filter, wordPairing_apply, dotProduct, allOnes, one_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hbit : ∀ z : Bit, (if z ≠ 0 then (1 : Bit) else 0) = z := by decide +kernel
    by_cases h : v i ≠ 0
    · simpa only [if_pos h, Nat.cast_one] using hbit (v i)
    · simpa only [if_neg h, Nat.cast_zero] using hbit (v i)
  have hones : ∀ g : Sum (Fin 4) QuadraticIndex, wordPairing allOnes (l2Generator g) = 0 := by decide +kernel
  have hb : l2CoefficientMap b = ∑ g, b g • l2Generator g := by
    funext i
    change (∑ g, b g * l2Generator g i) = _
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hz : wordPairing allOnes (l2CoefficientMap b) = 0 := by
    rw [hb]
    simp only [map_sum, map_smul, hones, smul_zero, Finset.sum_const_zero]
  have hw : (HammingWeight (l2CoefficientMap b) : Bit) = 0 := (hweight _).trans hz
  have hv := congrArg ZMod.val hw
  simpa only [ZMod.val_natCast, ZMod.val_zero] using hv
end QEC.Distillation.BK15