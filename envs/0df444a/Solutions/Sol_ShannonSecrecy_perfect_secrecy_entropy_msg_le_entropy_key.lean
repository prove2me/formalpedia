-- Prove2me | solution 1 for ShannonSecrecy.perfect_secrecy_entropy_msg_le_entropy_key
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:52:45.317448+00:00
-- url     : https://prove2.me/submissions/3331084a-b2d4-4c5e-bec1-a3ff2bf289ff

import Definitions.Def_shannon_secrecy_system

open ShannonSecrecy

namespace Ag4Aux_Shannon

lemma cryptoProb_eq {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (p : M → ℝ) (e : E) :
    cryptoProb C p e = ∑ m, p m * msgToCrypto C m e := by
  simp only [cryptoProb, msgToCrypto, Finset.mul_sum, mul_ite, mul_zero]

theorem iff_ps
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

theorem ent_le_log {α : Type*} [Fintype α] (p : α → ℝ) (hp : IsPMF p) (n : ℝ) (hn : 0 < n) :
    entropy p ≤ Real.log n + (Fintype.card α : ℝ) / n - 1 := by
  have key : ∀ a, Real.negMulLog (p a) ≤ p a * Real.log n + 1 / n - p a := by
    intro a
    rcases (hp.1 a).lt_or_eq with hpa | hpa
    · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (n * p a) by positivity)
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul hn.ne' hpa.ne'] at h1
      have h2 : p a * (1 / (n * p a)) = 1 / n := by field_simp
      rw [Real.negMulLog]
      nlinarith [h1, hpa]
    · rw [← hpa]; simp; positivity
  unfold entropy
  calc ∑ a, Real.negMulLog (p a) ≤ ∑ a, (p a * Real.log n + 1 / n - p a) :=
        Finset.sum_le_sum fun a _ => key a
    _ = Real.log n + (Fintype.card α : ℝ) / n - 1 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hp.2]
        simp [Finset.card_univ]; ring

theorem log_le_ent {α : Type*} [Fintype α] (q : α → ℝ) (hq0 : ∀ a, 0 ≤ q a)
    (hq1 : ∑ a, q a = 1) (n : ℝ) (hn : 0 < n) (hle : ∀ a, q a ≤ 1 / n) :
    Real.log n ≤ entropy q := by
  have key : ∀ a, q a * Real.log n ≤ Real.negMulLog (q a) := by
    intro a
    rcases (hq0 a).lt_or_eq with hqa | hqa
    · have : Real.log (q a) ≤ Real.log (1 / n) := Real.log_le_log hqa (hle a)
      rw [Real.log_div (by norm_num) hn.ne', Real.log_one] at this
      rw [Real.negMulLog]; nlinarith
    · rw [← hqa]; simp
  unfold entropy
  calc Real.log n = ∑ a, q a * Real.log n := by rw [← Finset.sum_mul, hq1, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ => key a

end Ag4Aux_Shannon

theorem solution
    {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]
    (C : Cipher M K E) (h : PerfectSecrecy C) (p : M → ℝ) (hp : IsPMF p) :
    entropy p ≤ entropy C.keyProb := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : entropy p = 0 := by simp [entropy]
    rw [h0]
    unfold entropy
    have hk1 : ∀ k, C.keyProb k ≤ 1 := by
      intro k
      rw [← C.keyProb_sum]
      exact Finset.single_le_sum (f := C.keyProb) (fun k _ => C.keyProb_nonneg k)
        (Finset.mem_univ k)
    exact Finset.sum_nonneg fun k _ => Real.negMulLog_nonneg (C.keyProb_nonneg k) (hk1 k)
  obtain ⟨m0⟩ := hM
  set n : ℝ := (Fintype.card M : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨m0⟩
  have heq := (Ag4Aux_Shannon.iff_ps C).mp h p hp
  -- total over messages is at most one
  have hsum : ∀ e, ∑ m, msgToCrypto C m e ≤ 1 := by
    intro e
    unfold msgToCrypto
    rw [Finset.sum_comm]
    calc ∑ k, ∑ m, (if C.encipher k m = e then C.keyProb k else 0)
        ≤ ∑ k, C.keyProb k := by
          apply Finset.sum_le_sum
          intro k _
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
          have hc : (Finset.univ.filter (fun m => C.encipher k m = e)).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro a ha b hb
            simp only [Finset.mem_filter] at ha hb
            exact C.encipher_injective k (ha.2.trans hb.2.symm)
          have : ((Finset.univ.filter (fun m => C.encipher k m = e)).card : ℝ) ≤ 1 := by
            exact_mod_cast hc
          nlinarith [C.keyProb_nonneg k]
      _ = 1 := C.keyProb_sum
  have hbound : ∀ e, msgToCrypto C m0 e ≤ 1 / n := by
    intro e
    have hs := hsum e
    have : ∑ m, msgToCrypto C m e = n * msgToCrypto C m0 e := by
      rw [Finset.sum_congr rfl (fun m _ => (heq m e).trans (heq m0 e).symm)]
      simp [hn]
    rw [this] at hs
    rw [le_div_iff₀ hnpos]; linarith
  have hk : ∀ k, C.keyProb k ≤ 1 / n := by
    intro k
    refine le_trans ?_ (hbound (C.encipher k m0))
    unfold msgToCrypto
    have := Finset.single_le_sum (f := fun k' => if C.encipher k' m0 = C.encipher k m0 then C.keyProb k' else 0)
      (fun k' _ => by split_ifs; exacts [C.keyProb_nonneg k', le_rfl]) (Finset.mem_univ k)
    simpa using this
  have h1 := Ag4Aux_Shannon.ent_le_log p hp n hnpos
  have h2 := Ag4Aux_Shannon.log_le_ent C.keyProb C.keyProb_nonneg C.keyProb_sum n hnpos hk
  have h3 : (Fintype.card M : ℝ) / n = 1 := by rw [← hn]; exact div_self hnpos.ne'
  linarith
