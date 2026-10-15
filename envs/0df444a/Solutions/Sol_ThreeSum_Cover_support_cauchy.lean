-- Prove2me | solution 1 for ThreeSum.Cover.support_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:02.591323+00:00
-- url     : https://prove2.me/submissions/1501037f-fa26-44ab-845f-30ae2c1ee3c6

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite cover bounds

Finite, exact lemmas for the second-moment argument, deterministic averaging,
and composition used in the proposed construction.  A hypothesis about a
particular local hash family is a mathematical obligation, not an asserted
implementation or running-time theorem.
-/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

/-- Cauchy--Schwarz with the cardinality of the actual support. -/
theorem support_cauchy_sourceProof {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    (∑ ω, f ω) ^ 2 ≤
      ((univ.filter fun ω => f ω ≠ 0).card : ℝ) * ∑ ω, (f ω) ^ 2 := by
  classical
  let s := univ.filter fun ω => f ω ≠ 0
  have hsum : ∑ ω ∈ s, f ω = ∑ ω, f ω := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro ω _
    split_ifs with h
    · rfl
    · simp_all
  have hsq : ∑ ω ∈ s, (f ω) ^ 2 = ∑ ω, (f ω) ^ 2 := by
    simp only [s, sum_filter]
    apply sum_congr rfl
    intro ω _
    split_ifs with h
    · rfl
    · simp_all
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  rw [hsum, hsq] at h
  exact h









































































end ThreeSum.Cover

end

universe u_1

theorem solution : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] (f : Ω → Real),
  @LE.le.{0} Real Real.instLE
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (∑ ω : Ω, f ω)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{u_1} Ω
          {ω : Ω | @Ne.{1} Real (f ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))}))
      (∑ ω : Ω,
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (f ω)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @ThreeSum.Cover.support_cauchy_sourceProof

#print axioms solution
