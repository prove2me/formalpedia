-- Prove2me | solution 1 for TaoFivePrimes.rh123_translation_tail60
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:36:29.040137+00:00
-- url     : https://prove2.me/submissions/4e40e7eb-69df-4e4e-8650-7a86035916b2

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Theorems.Thm_TaoFivePrimes_rh123_translation_tail_group0
import Theorems.Thm_TaoFivePrimes_rh123_translation_tail_group1
import Theorems.Thm_TaoFivePrimes_rh123_translation_tail_group2
import Theorems.Thm_TaoFivePrimes_rh123_translation_tail_group3
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 20,
    (10^32:ℤ)*|RH320TranslationArithmetic.numerator 246 (10^40) (n.val+40)| ≤
      (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n
  · simpa using TaoFivePrimes.rh123_translation_tail_group0 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group0 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group0 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group0 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group0 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group1 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group1 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group1 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group1 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group1 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group2 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group2 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group2 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group2 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group2 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group3 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group3 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group3 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group3 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_tail_group3 (⟨4,by norm_num⟩:Fin 5)
