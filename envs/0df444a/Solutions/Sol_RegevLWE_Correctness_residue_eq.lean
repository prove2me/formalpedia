-- Prove2me | solution 1 for RegevLWE.Correctness.residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:36:27.639125+00:00
-- url     : https://prove2.me/submissions/e9346105-c3f6-4548-ac2a-7ccda9958327

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

set_option autoImplicit false
open Matrix RegevLWE.Correctness

theorem solution {p : ℕ} [NeZero p] {n m : ℕ} (a : Fin m → Fin n → ZMod p)
    (s : Fin n → ZMod p) (e : Fin m → ZMod p) (S : Finset (Fin m)) :
    (encrypt (publicKey a s e) 0 S).2 - (encrypt (publicKey a s e) 0 S).1 ⬝ᵥ s
        = ∑ i ∈ S, e i ∧
      (encrypt (publicKey a s e) 1 S).2 - (encrypt (publicKey a s e) 1 S).1 ⬝ᵥ s
        = ((p / 2 : ℕ) : ZMod p) + ∑ i ∈ S, e i := by
  have key : ∑ i ∈ S, (a i ⬝ᵥ s + e i) - (∑ i ∈ S, a i) ⬝ᵥ s = ∑ i ∈ S, e i := by
    rw [Finset.sum_add_distrib, sum_dotProduct]
    ring
  constructor
  · simp only [encrypt, publicKey]
    simpa using key
  · simp only [encrypt, publicKey]
    simp only [if_true]
    linear_combination key

