-- Prove2me | solution 1 for PI.WickFormula.comm_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:40.267741+00:00
-- url     : https://prove2.me/submissions/4066aab0-0633-4cea-8f62-c99f0d4374c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA]
namespace PI.WickFormula
theorem _root_.solution (b c : AA) (t : k) (h : b * c = c * b + algebraMap k AA t) (n : ℕ) :
    b * c ^ (n + 1) = c ^ (n + 1) * b + (((n : k) + 1) * t) • c ^ n := by
  induction n with
  | zero => simp [h, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    calc b * c ^ (n + 1 + 1) = (b * c ^ (n + 1)) * c := by rw [pow_succ c (n + 1), mul_assoc]
      _ = (c ^ (n + 1) * b + (((n : k) + 1) * t) • c ^ n) * c := by rw [ih]
      _ = c ^ (n + 1) * (b * c) + (((n : k) + 1) * t) • (c ^ n * c) := by
          rw [add_mul, mul_assoc, smul_mul_assoc]
      _ = c ^ (n + 1) * (c * b + algebraMap k AA t) + (((n : k) + 1) * t) • c ^ (n + 1) := by
          rw [h, ← pow_succ]
      _ = c ^ (n + 1 + 1) * b + t • c ^ (n + 1) + (((n : k) + 1) * t) • c ^ (n + 1) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      _ = c ^ (n + 1 + 1) * b + ((((n + 1 : ℕ) : k) + 1) * t) • c ^ (n + 1) := by
          rw [add_assoc, ← add_smul]
          congr 2
          push_cast
          ring
end PI.WickFormula
