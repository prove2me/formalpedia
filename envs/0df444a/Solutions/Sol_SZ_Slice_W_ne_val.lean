-- Prove2me | solution 1 for SZ.Slice.W_ne_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:38:38.389479+00:00
-- url     : https://prove2.me/submissions/8671f37c-b5b1-422d-a77e-ee203f159255

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
import Definitions.Def_SZ_SliceHygiene
import Theorems.Thm_SZ_Slice_stt_val
import Theorems.Thm_SZ_Slice_stt_snd_lower
import Theorems.Thm_SZ_Slice_val_inj


set_option autoImplicit false
open SZ
open SZ.Slice
variable {S : Slice}
namespace SZ.Slice
theorem _root_.solution (he : S.e = (S.m : ℤ) - 1) {j k₀ : ℤ} (hk : 1 ≤ k₀)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) (k : ℕ) {p q : ℤ}
    (hq : q ≤ (S.m : ℤ)) : S.W (S.w0 j k₀) k ≠ (p : ℝ) + (q : ℝ) * S.sq := by
  intro hcon
  rw [stt_val he] at hcon
  obtain ⟨-, h2⟩ := S.val_inj hcon
  have hlow := stt_snd_lower he hk h0 h1 k
  have hmz : (3 : ℤ) ≤ (S.m : ℤ) := by exact_mod_cast S.three_le
  have hpow : (S.m : ℤ) ≤ (S.m : ℤ) ^ (k + 1) := by
    calc (S.m : ℤ) = (S.m : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ (S.m : ℤ) ^ (k + 1) := pow_le_pow_right₀ (by omega) (by omega)
  have hpm : (S.m : ℤ) ≤ S.p * (S.m : ℤ) ^ (k + 1) :=
    le_trans hpow (le_mul_of_one_le_left (by positivity) (by have := S.two_le_p; omega))
  rw [h2] at hlow
  linarith
end SZ.Slice
