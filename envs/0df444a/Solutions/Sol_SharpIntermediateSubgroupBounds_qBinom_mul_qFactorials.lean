-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.qBinom_mul_qFactorials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:26.760934+00:00
-- url     : https://prove2.me/submissions/85196602-df7d-4db1-83c5-8aec32e320a9

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_succ
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
private theorem pow_sub_one_add_mul_pow_sub_one {q a b : ℕ} (hq : 1 ≤ q) :
    (q ^ a - 1) + q ^ a * (q ^ b - 1) = q ^ (a + b) - 1 := by
  have ha : 1 ≤ q ^ a := one_le_pow₀ hq
  have hb : 1 ≤ q ^ b := one_le_pow₀ hq
  have hab : q ^ a ≤ q ^ a * q ^ b := by
    simpa using Nat.mul_le_mul_left (q ^ a) hb
  rw [pow_add, Nat.mul_sub_left_distrib, mul_one, add_comm]
  exact tsub_add_tsub_cancel hab ha
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          by_cases htop : k = n
          · subst k
            rw [qBinom_succ_succ, qBinom_self,
              qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
            simp [qFactorial_succ]
          · have hklt : k < n := lt_of_le_of_ne hkn htop
            have hk1 : k + 1 ≤ n := by omega
            have hsub : n - k = (n - (k + 1)) + 1 := by omega
            rw [qBinom_succ_succ, qFactorial_succ, Nat.succ_sub_succ_eq_sub, hsub,
              qFactorial_succ]
            calc
              (qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)) *
                    (qFactorial q k * (q ^ (k + 1) - 1)) *
                    (qFactorial q (n - (k + 1)) * (q ^ (n - (k + 1) + 1) - 1)) =
                  (qBinom q n k * qFactorial q k * qFactorial q (n - k)) *
                      (q ^ (k + 1) - 1) +
                    q ^ (k + 1) *
                      (qBinom q n (k + 1) * qFactorial q (k + 1) *
                        qFactorial q (n - (k + 1))) *
                      (q ^ (n - k) - 1) := by
                        rw [qFactorial_succ, hsub, qFactorial_succ]
                        ring
              _ = qFactorial q n * (q ^ (k + 1) - 1) +
                    q ^ (k + 1) * qFactorial q n * (q ^ (n - k) - 1) := by
                      rw [ih hkn, ih hk1]
              _ = qFactorial q n * (q ^ (n + 1) - 1) := by
                    have hexp : k + 1 + (n - k) = n + 1 := by omega
                    calc
                      qFactorial q n * (q ^ (k + 1) - 1) +
                          q ^ (k + 1) * qFactorial q n * (q ^ (n - k) - 1) =
                          qFactorial q n * ((q ^ (k + 1) - 1) +
                            q ^ (k + 1) * (q ^ (n - k) - 1)) := by ring
                      _ = qFactorial q n * (q ^ ((k + 1) + (n - k)) - 1) := by
                        rw [pow_sub_one_add_mul_pow_sub_one (by omega)]
                      _ = qFactorial q n * (q ^ (n + 1) - 1) := by rw [hexp]
              _ = qFactorial q (n + 1) := by rw [qFactorial_succ]
end SharpIntermediateSubgroupBounds
