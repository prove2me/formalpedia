-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.log_sq_mul_pow_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:54:59.884374+00:00
-- url     : https://prove2.me/submissions/249e5a82-5f87-4052-b9ee-3811c3cd5617

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_self_le_base_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_self_pow_le_base_pow_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_le_exponent_of_le_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q A n e : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n) :
    Nat.log q ((A * n ^ e) * (A * n ^ e) + 1) ≤
      2 * (A + n * e) + 1 := by
  have hLocal : A * n ^ e ≤ q ^ (A + n * e) := by
    calc
      A * n ^ e ≤ q ^ A * q ^ (n * e) :=
        Nat.mul_le_mul (self_le_base_pow q A hq)
          (self_pow_le_base_pow_mul q n e hq)
      _ = q ^ (A + n * e) := by rw [pow_add]
  have hLocalPositive : 0 < A * n ^ e :=
    Nat.mul_pos hA (Nat.pow_pos hn)
  have hSquare : (A * n ^ e) * (A * n ^ e) ≤
      q ^ (2 * (A + n * e)) := by
    calc
      (A * n ^ e) * (A * n ^ e) ≤
          q ^ (A + n * e) * q ^ (A + n * e) :=
        Nat.mul_le_mul hLocal hLocal
      _ = q ^ (2 * (A + n * e)) := by
        rw [← pow_add]
        congr 1
        omega
  have hSquarePositive : 0 < (A * n ^ e) * (A * n ^ e) :=
    Nat.mul_pos hLocalPositive hLocalPositive
  have hWithOne : (A * n ^ e) * (A * n ^ e) + 1 ≤
      q ^ (2 * (A + n * e) + 1) := by
    calc
      (A * n ^ e) * (A * n ^ e) + 1 ≤
          2 * ((A * n ^ e) * (A * n ^ e)) := by omega
      _ ≤ q * ((A * n ^ e) * (A * n ^ e)) :=
        Nat.mul_le_mul_right _ hq
      _ ≤ q * q ^ (2 * (A + n * e)) :=
        Nat.mul_le_mul_left q hSquare
      _ = q ^ (2 * (A + n * e) + 1) := by
        rw [pow_succ', Nat.mul_comm]
  exact log_le_exponent_of_le_pow q _ _ (by omega) hWithOne
end QEC.Coding.TannerLiftedProduct
