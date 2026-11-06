-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.count_bind_replicate_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:34.120912+00:00
-- url     : https://prove2.me/submissions/73e6f872-66d7-4eec-9dca-948e195d9f16

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
namespace QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
theorem _root_.solution (s : Multiset alpha) (f : alpha → beta)
    (w : alpha → Nat) (q : beta) :
    Multiset.count q (s.bind fun a => Multiset.replicate (w a) (f a)) =
      ∑ a ∈ s.toFinset, (if f a = q then w a else 0) * s.count a := by
  classical
  rw [Multiset.count_bind]
  simp only [Multiset.count_replicate]
  simpa [Nat.mul_comm] using
    Finset.sum_multiset_map_count s (fun a => if f a = q then w a else 0)
end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
