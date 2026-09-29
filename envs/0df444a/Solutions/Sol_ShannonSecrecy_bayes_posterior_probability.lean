-- Prove2me | solution 1 for ShannonSecrecy.bayes_posterior_probability
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T21:35:10.60395+00:00
-- url     : https://prove2.me/submissions/54d32ce8-6cc0-4f25-a398-17124f88721e

import Definitions.Def_shannon_secrecy_system

set_option autoImplicit false

open ShannonSecrecy
theorem solution
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (p : M → ℝ) (e : E) (m : M) :
    cryptoProb C p e = ∑ m' : M, p m' * msgToCrypto C m' e ∧
      postProb C p e m = p m * msgToCrypto C m e / cryptoProb C p e := by
  refine ⟨?_, ?_⟩
  · simp only [cryptoProb, msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]
  · simp only [postProb, msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]
