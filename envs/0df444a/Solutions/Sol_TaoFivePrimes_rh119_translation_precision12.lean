-- Prove2me | solution 1 for TaoFivePrimes.rh119_translation_precision12
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:35:41.062429+00:00
-- url     : https://prove2.me/submissions/07445e58-6f11-45a8-9d95-59cbd685537e

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh119_translation_precision12_0_9
import Theorems.Thm_TaoFivePrimes_rh119_translation_precision12_10_19
import Theorems.Thm_TaoFivePrimes_rh119_translation_precision12_20_29
import Theorems.Thm_TaoFivePrimes_rh119_translation_precision12_30_39

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 10
      else if n.val<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH304TranslationArithmetic.numerator 238 (10^38) n.val-
        TaoFivePrimes_RH119RoundedCoefficients12.getD n.val 0*(RH304TranslationArithmetic.denominator:ℤ)| ≤
          (RH304TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨0,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨1,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨2,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨3,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨4,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨5,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨6,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨7,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨8,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_0_9 (⟨9,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨0,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨1,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨2,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨3,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨4,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨5,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨6,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨7,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨8,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_10_19 (⟨9,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨0,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨1,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨2,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨3,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨4,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨5,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨6,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨7,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨8,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_20_29 (⟨9,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨0,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨1,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨2,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨3,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨4,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨5,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨6,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨7,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨8,by norm_num⟩:Fin 10)
  · simpa only [Fin.val_mk, Nat.reduceAdd] using TaoFivePrimes.rh119_translation_precision12_30_39 (⟨9,by norm_num⟩:Fin 10)
