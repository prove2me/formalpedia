-- Prove2me | solution 1 for TaoFivePrimes.rh123_translation_precision12
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:36:29.144983+00:00
-- url     : https://prove2.me/submissions/ce1d40df-2926-40c2-ac4f-8475a8c15d70

import Definitions.Def_TaoFivePrimes_RH320TranslationArithmetic
import Definitions.Def_TaoFivePrimes_RH123RoundedCoefficients12
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group0
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group1
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group2
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group3
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group4
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group5
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group6
import Theorems.Thm_TaoFivePrimes_rh123_translation_precision_group7
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ n : Fin 40,
    (if n.val<20 then (1:ℤ) else if n.val<25 then 10 else if n.val<30 then 10^4 else 10^8) *
      |(10^12:ℤ)*RH320TranslationArithmetic.numerator 246 (10^40) n.val-
        TaoFivePrimes_RH123RoundedCoefficients12.getD n.val 0*(RH320TranslationArithmetic.denominator:ℤ)| ≤
          (RH320TranslationArithmetic.denominator:ℤ) := by
  intro n
  fin_cases n
  · simpa using TaoFivePrimes.rh123_translation_precision_group0 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group0 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group0 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group0 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group0 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group1 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group1 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group1 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group1 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group1 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group2 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group2 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group2 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group2 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group2 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group3 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group3 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group3 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group3 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group3 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group4 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group4 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group4 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group4 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group4 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group5 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group5 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group5 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group5 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group5 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group6 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group6 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group6 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group6 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group6 (⟨4,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group7 (⟨0,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group7 (⟨1,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group7 (⟨2,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group7 (⟨3,by norm_num⟩:Fin 5)
  · simpa using TaoFivePrimes.rh123_translation_precision_group7 (⟨4,by norm_num⟩:Fin 5)
