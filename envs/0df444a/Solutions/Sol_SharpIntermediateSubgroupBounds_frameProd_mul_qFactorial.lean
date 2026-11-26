-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.frameProd_mul_qFactorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:22.294805+00:00
-- url     : https://prove2.me/submissions/966e4b91-47f4-4b34-bc01-a1338ebd73a3

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Theorems.Thm_SharpIntermediateSubgroupBounds_qFactorial_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_frameProd_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_framePower_succ
section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
private theorem pow_sub_pow_eq_mul_sub {q n k : ℕ} (hk : k ≤ n) :
    q ^ n - q ^ k = q ^ k * (q ^ (n - k) - 1) := by
  nth_rewrite 1 [show n = k + (n - k) by omega]
  rw [pow_add, Nat.mul_sub_left_distrib]
  simp
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q n k : ℕ} (hk : k ≤ n) :
    frameProd q n k * qFactorial q (n - k) =
      framePower q k * qFactorial q n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkn : k ≤ n := by omega
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      rw [frameProd_succ, pow_sub_pow_eq_mul_sub hkn, framePower_succ]
      calc
        frameProd q n k * (q ^ k * (q ^ (n - k) - 1)) *
              qFactorial q (n - (k + 1)) =
            q ^ k * (frameProd q n k *
              (qFactorial q (n - (k + 1)) * (q ^ (n - k) - 1))) := by ring
        _ = q ^ k * (frameProd q n k * qFactorial q (n - k)) := by
          rw [hsub, qFactorial_succ]
        _ = q ^ k * (framePower q k * qFactorial q n) := by rw [ih hkn]
        _ = framePower q k * q ^ k * qFactorial q n := by ring
end SharpIntermediateSubgroupBounds
