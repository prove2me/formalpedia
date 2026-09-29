-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_gt_47_adapter_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T11:28:07.572707+00:00
-- url     : https://prove2.me/submissions/05eb8a4a-8d41-4ebf-9db0-1aa6134a9c59

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_gt_47_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (ha : 5 ≤ a) (hb : 3 ≤ b)
    (hc : 4 ≤ c) (he : 1 ≤ e) : 47 < q4 := by
  by_contra h
  have hq4le : q4 ≤ 47 := by omega
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_gt_47_v2
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime
    hq4gt hq4le ha hb hc he
