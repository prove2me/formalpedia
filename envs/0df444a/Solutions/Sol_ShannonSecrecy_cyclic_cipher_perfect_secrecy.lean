-- Prove2me | solution 1 for ShannonSecrecy.cyclic_cipher_perfect_secrecy
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T21:35:10.533889+00:00
-- url     : https://prove2.me/submissions/63738bd1-de3d-4469-bdb0-abeb74c498b3

import Definitions.Def_shannon_secrecy_system

set_option autoImplicit false

open ShannonSecrecy
theorem solution (n : ℕ) [NeZero n] :
    PerfectSecrecy (cyclicCipher n) := by
  intro p hp e _ m
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- exactly one key `e - m` sends `m` to `e`
  have key : ∀ m' : ZMod n, (∑ k : ZMod n,
      if (cyclicCipher n).encipher k m' = e then p m' * (cyclicCipher n).keyProb k else 0)
        = p m' * (n : ℝ)⁻¹ := by
    intro m'
    rw [Finset.sum_eq_single (e - m')]
    · simp [cyclicCipher]
    · intro k _ hk
      rw [if_neg]
      intro hke
      apply hk
      simp only [cyclicCipher] at hke
      rw [← hke]; ring
    · simp
  have hcp : cryptoProb (cyclicCipher n) p e = (n : ℝ)⁻¹ := by
    unfold cryptoProb
    simp_rw [key, ← Finset.sum_mul, hp.2, one_mul]
  unfold postProb
  rw [key, hcp, mul_div_assoc, div_self (inv_ne_zero hn0), mul_one]
