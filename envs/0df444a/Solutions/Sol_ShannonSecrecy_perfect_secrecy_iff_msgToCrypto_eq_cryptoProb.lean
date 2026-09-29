-- Prove2me | solution 1 for ShannonSecrecy.perfect_secrecy_iff_msgToCrypto_eq_cryptoProb
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T22:28:20.388189+00:00
-- url     : https://prove2.me/submissions/939f2df1-8223-4af8-8fe9-c680ea7ff8fb

import Mathlib
import Definitions.Def_shannon_secrecy_system

set_option autoImplicit false

open ShannonSecrecy

/-- `P(E)` is affine in the message distribution. -/
lemma cryptoProb_eq {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (p : M → ℝ) (e : E) :
    cryptoProb C p e = ∑ m, p m * msgToCrypto C m e := by
  simp only [cryptoProb, msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]

theorem solution
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) :
    PerfectSecrecy C ↔
      ∀ p : M → ℝ, IsPMF p → ∀ (m : M) (e : E), msgToCrypto C m e = cryptoProb C p e := by
  classical
  have hmc_nn : ∀ m e, 0 ≤ msgToCrypto C m e := fun m e =>
    Finset.sum_nonneg fun k _ => by split_ifs; exacts [C.keyProb_nonneg k, le_rfl]
  have hnum : ∀ (p : M → ℝ) e m,
      (∑ k : K, if C.encipher k m = e then p m * C.keyProb k else 0) = p m * msgToCrypto C m e := by
    intro p e m; simp only [msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]
  constructor
  · intro h
    -- Step 1: for any distribution `q` with `q m > 0`, `P_m(e) = P_q(e)`.
    have step1 : ∀ q : M → ℝ, IsPMF q → ∀ m e, 0 < q m → msgToCrypto C m e = cryptoProb C q e := by
      intro q hq m e hqm
      by_cases hce : cryptoProb C q e = 0
      · rw [hce]
        rw [cryptoProb_eq] at hce
        have hterm : q m * msgToCrypto C m e = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun m' _ => mul_nonneg (hq.1 m') (hmc_nn m' e))).mp hce m
            (Finset.mem_univ m)
        rcases mul_eq_zero.mp hterm with h0 | h0
        · linarith
        · exact h0
      · have hpost := h q hq e hce m
        unfold postProb at hpost
        rw [hnum, div_eq_iff hce] at hpost
        have := mul_left_cancel₀ hqm.ne' (by linarith [hpost] : q m * msgToCrypto C m e = q m * cryptoProb C q e)
        exact this
    intro p hp m e
    -- mix `p` with the point mass at `m`
    set q : M → ℝ := fun x => (p x + (if x = m then 1 else 0)) / 2 with hqdef
    have hq : IsPMF q := by
      refine ⟨fun x => by simp only [hqdef]; have := hp.1 x; split_ifs <;> linarith, ?_⟩
      simp only [hqdef, ← Finset.sum_div, Finset.sum_add_distrib, hp.2, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      norm_num
    have hqm : 0 < q m := by
      show 0 < (p m + (if m = m then 1 else 0)) / 2
      rw [if_pos rfl]; linarith [hp.1 m]
    have h1 := step1 q hq m e hqm
    have hq_eq : cryptoProb C q e = (cryptoProb C p e + msgToCrypto C m e) / 2 := by
      rw [cryptoProb_eq, cryptoProb_eq, hqdef]
      simp only [add_mul, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_add_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hq_eq] at h1
    linarith
  · intro h p hp e hce m
    unfold postProb
    rw [hnum, h p hp m e, mul_div_assoc, div_self hce, mul_one]
