-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P89.balanced_cluster_size
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:38:51.551751+00:00
-- url     : https://prove2.me/submissions/d97b1a57-5a8a-4f3b-af03-4cd11222f74b

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)
open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

namespace Aux_Q01_balanced_cluster_size
open QAlgorithms.Papers.Independent.Intakenext100.P89

theorem size_eq (k : ℕ) : balancedSize k = 2 ^ k + 2 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    show 2 * balancedSize n - 2 = 2 ^ (n + 1) + 2
    rw [ih, pow_succ]
    omega

end Aux_Q01_balanced_cluster_size

open QAlgorithms.Papers.Independent.Intakenext100.P89 in
theorem solution (k : ℕ) :
    balancedSize k = 2 ^ k + 2 ∧
    (∀ N : ℕ, 3 ≤ N → (N ≤ balancedSize k ↔ Nat.clog 2 (N - 2) ≤ k)) := by
  refine ⟨Aux_Q01_balanced_cluster_size.size_eq k, ?_⟩
  intro N hN
  rw [Aux_Q01_balanced_cluster_size.size_eq k, Nat.clog_le_iff_le_pow (by norm_num)]
  omega
