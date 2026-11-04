-- Prove2me | solution 1 for ThreeSum.ModuloRuntime.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:49.869226+00:00
-- url     : https://prove2.me/submissions/832c2f36-5167-4140-b4af-488cd6b786f5

import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Theorems.Thm_ThreeSum_ModuloRuntime_capacity_mono

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloRuntime
open LightModuloCounts KaratsubaInterface
namespace ThreeSum.ModuloRuntime
theorem _root_.solution {p q : ℕ} (h : p ≤ q) (N U : ℕ) :
    word p N U ≤ word q N U := by
  have hc := Nat.pow_le_pow_left (capacity_mono h) 3
  have hk : LightKaratsuba.wordBound (capacity p) N ≤
      LightKaratsuba.wordBound (capacity q) N := by
    unfold LightKaratsuba.wordBound
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 128 hc)
  unfold word
  omega
end ThreeSum.ModuloRuntime
